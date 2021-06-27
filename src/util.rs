//! Support functions that don't belong anywhere else or use unsafe code.

use fnv::FnvHasher;
use std::collections;
use std::hash::BuildHasherDefault;
use std::hash::Hash;
use std::ops::Index;
use std::ops::Range;
use std::ptr;
use std::slice;
use core::fmt::Debug;

/// Type alias for hashmaps to allow swapping out the implementation.
pub type HashMap<K, V> = collections::HashMap<K, V, BuildHasherDefault<FnvHasher>>;
/// Type alias for hashsets to allow swapping out the implementation.
pub type HashSet<K> = collections::HashSet<K, BuildHasherDefault<FnvHasher>>;

/// Create a new empty map.
pub fn new_map<K, V>() -> HashMap<K, V>
    where K: Eq + Hash
{
    HashMap::<K, V>::with_hasher(Default::default())
}

/// Create a new empty set.
pub fn new_set<K>() -> HashSet<K>
    where K: Eq + Hash
{
    HashSet::<K>::with_hasher(Default::default())
}

/// Quickly determine if two references are pointing at the same object.
///
/// You almost always want to pass a type argument when calling this function in
/// order to force `Deref` coercions to run.
///
///   ```
///   # use util;
///   # use std::sync::Arc;
///   let a1 = Arc::new("Hello, world".to_string());
///   let a2 = a1.clone();
///   // BAD: resolves as Arc<String>, we've learned we have two Arcs
///   assert!(!util::ptr_eq(&a1, &a2));
///   // GOOD: forcing deref to String, we have only one of those
///   assert!(util::ptr_eq::<String>(&a1, &a2));
///   ```
pub fn ptr_eq<T>(x: &T, y: &T) -> bool {
    x as *const _ == y as *const _
}

/// Empty a vector of a POD type without checking each element for droppability.
pub fn fast_clear<T: Copy>(vec: &mut Vec<T>) {
    unsafe {
        vec.set_len(0);
    }
}

// emprically, *most* copies in the verifier where fast_extend and copy_portion
// are used are 1-2 bytes
unsafe fn short_copy<T>(src: *const T, dst: *mut T, count: usize) {
    match count {
        1 => ptr::write(dst, ptr::read(src)),
        2 => ptr::write(dst as *mut [T; 2], ptr::read(src as *const [T; 2])),
        _ => ptr::copy_nonoverlapping(src, dst, count),
    }
}

/// Appends a POD slice to a vector with a simple `memcpy`.
pub fn fast_extend<T: Copy>(vec: &mut Vec<T>, other: &[T]) {
    vec.reserve(other.len());
    unsafe {
        let len = vec.len();
        short_copy(other.get_unchecked(0),
                   vec.get_unchecked_mut(len),
                   other.len());
        vec.set_len(len + other.len());
    }
}

/// Appends a slice of a byte vector to the end of the same vector.
#[inline(always)]
pub fn copy_portion(vec: &mut Vec<u8>, from: Range<usize>) {
    let Range { start: copy_start, end: copy_end } = from;
    &vec[from]; // for the bounds check
    unsafe {
        let copy_len = copy_end - copy_start;
        vec.reserve(copy_len);

        let old_len = vec.len();
        let copy_from = vec.as_ptr().offset(copy_start as isize);
        let copy_to = vec.as_mut_ptr().offset(old_len as isize);
        short_copy(copy_from, copy_to, copy_len);
        vec.set_len(old_len + copy_len);
    }
}

// Rust already assumes you're on a twos-complement byte-addressed pure-endian
// machine. A chapter header is CRLF+ $ ( CRLF+ #*#...#*#, 79 total punctuation.
// Thus, it has #*#* or *#*# on any 32*19-bit boundary

// find a maximal 4-byte aligned slice within a larger byte slice
fn aligned_part(buffer: &[u8]) -> (usize, &[u32]) {
    let mut sptr = buffer.as_ptr() as usize;
    let mut eptr = sptr + buffer.len();

    if buffer.len() < 4 {
        return (0, Default::default());
    }

    let offset = sptr.wrapping_neg() & 3;
    sptr += offset; // just checked this won't overflow
    eptr -= eptr & 3; // cannot overflow by construction

    unsafe { (offset, slice::from_raw_parts(sptr as *const u32, (eptr - sptr) / 4)) }
}

/// Search for a properly formatted set.mm-style chapter header in a byte
/// buffer, taking advantage of a known repetetive 79-byte substring with a
/// Boyer-Moore search.
///
/// This runs on the full file on every reload, but it's also pretty good at
/// running at full memory bandwidth.
#[inline(never)]
pub fn find_chapter_header(mut buffer: &[u8]) -> Option<usize> {
    // returns something pointing at four consequtive puncts, guaranteed to find
    // if there is a run of 79
    fn hunt(buffer: &[u8]) -> Option<usize> {
        let (offset, aligned) = aligned_part(buffer);

        let mut pp = 0;
        while pp < aligned.len() {
            let word = aligned[pp];
            if word == 0x2a232a23 || word == 0x232a232a {
                return Some(offset + pp * 4);
            }
            pp += 19;
        }

        return None;
    }

    const LANDING_STRIP: &'static [u8] =
        b"#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#";

    fn is_real(buffer: &[u8], mut midp: usize) -> Option<usize> {
        // backtrack to the beginning of the line
        while midp > 0 && (buffer[midp] == b'#' || buffer[midp] == b'*') {
            midp -= 1;
        }

        // make sure we reached a CR or LF
        if buffer[midp] != b'\r' && buffer[midp] != b'\n' {
            return None;
        }

        // make sure the line is what we think it is
        if buffer.len() - midp < LANDING_STRIP.len() + 1 ||
           &buffer[midp + 1..midp + 1 + LANDING_STRIP.len()] != LANDING_STRIP {
            return None;
        }

        // skip CRLF
        while midp > 0 && (buffer[midp] == b'\r' || buffer[midp] == b'\n') {
            midp -= 1;
        }
        // make sure we reached [CRLF] $(
        if midp >= 2 && buffer[midp] == b'(' && buffer[midp - 1] == b'$' &&
           (buffer[midp - 2] == b'\r' || buffer[midp - 2] == b'\n') {
            Some(midp - 1)
        } else {
            None
        }
    }

    let mut offset = 0;
    loop {
        // quickly scan for a plausible offset into the horizontal line
        if let Some(mix) = hunt(buffer) {
            // check if we actually found a chapter heading
            if let Some(chap) = is_real(buffer, mix) {
                return Some(chap + offset);
            } else {
                buffer = &buffer[mix + 1..];
                offset += mix + 1;
            }
        } else {
            return None;
        }
    }
}

/// Emulating Vec over a pair
#[derive(Clone, Copy, Debug)]
pub enum PairVec<T> {
	/// Empty vec
	Zero,
	/// Vec with one element
	One (T),
	/// Vec with two elements
	Two (T, T),
}

impl<T> Index<usize> for PairVec<T> {
	type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
		match (self, index) {
			(PairVec::One(t), 0) | (PairVec::Two(t, _), 0) | (PairVec::Two(_, t), 1) => t,
			_ => panic!("Index out of range in PairVec!"),
		}
    }
}

impl<T: Copy+Debug> PairVec<T> {
	pub fn prepend(&self, t: T) -> Self {
		match self {
			PairVec::Zero => PairVec::One(t),
			PairVec::One(u) => { 
				println!("+++ Prepending {:?} to {:?}", t, u);
				PairVec::Two(t, *u)},
			_ => panic!("PairVec overflow!"),
		}
	}
}

/// An iterator for the Vec over a pair emulation
pub struct PairVecIter<'a, T> {
	data: &'a PairVec<T>,
    index: usize,
}

impl<'a, T> IntoIterator for &'a PairVec<T> {
    type Item = &'a T;
    type IntoIter = PairVecIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        PairVecIter {
            data: self,
            index: 0,
        }
    }
}

impl<'a, T> Iterator for PairVecIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
		self.index += 1;
		match self {
			PairVecIter { data: PairVec::One(t), index: 1 } | PairVecIter { data: PairVec::Two(t,_), index: 1 } | PairVecIter { data: PairVec::Two(_,t), index: 2 } => Some(t),
			_ => None,
		}
    }
}
