use fnv::FnvHasher;
use std::collections;
use std::hash::BuildHasherDefault;
use std::hash::Hash;
use std::hash::Hasher;
use std::ops::Range;
use std::ptr;
use std::slice;

pub type HashMap<K, V> = collections::HashMap<K, V, BuildHasherDefault<FnvHasher>>;
pub type HashSet<K> = collections::HashSet<K, BuildHasherDefault<FnvHasher>>;

pub fn new_map<K, V>() -> HashMap<K, V>
    where K: Eq + Hash
{
    HashMap::<K, V>::with_hasher(Default::default())
}

pub fn new_set<K>() -> HashSet<K>
    where K: Eq + Hash
{
    HashSet::<K>::with_hasher(Default::default())
}

pub fn ptr_eq<T>(x: &T, y: &T) -> bool {
    x as *const _ == y as *const _
}

// avoids dropping overhead

pub fn fast_clear<T: Copy>(vec: &mut Vec<T>) {
    unsafe {
        vec.set_len(0);
    }
}

pub fn fast_extend<T: Copy>(vec: &mut Vec<T>, other: &[T]) {
    vec.reserve(other.len());
    unsafe {
        let len = vec.len();
        ptr::copy_nonoverlapping(other.get_unchecked(0),
                                 vec.get_unchecked_mut(len),
                                 other.len());
        vec.set_len(len + other.len());
    }
}

pub fn copy_portion(vec: &mut Vec<u8>, from: Range<usize>) {
    let Range { start: copy_start, end: copy_end } = from.clone();
    &vec[from]; // for the bounds check
    unsafe {
        let copy_len = copy_end - copy_start;
        vec.reserve(copy_len);

        let old_len = vec.len();
        let copy_from = vec.as_ptr().offset(copy_start as isize);
        let copy_to = vec.as_mut_ptr().offset(old_len as isize);
        ptr::copy_nonoverlapping(copy_from, copy_to, copy_len);
        vec.set_len(old_len + copy_len);
    }
}

// rust already assumes you're on a twos-complement byte-addressed pure-endian machine...
// a chapter header is CRLF+ $ ( CRLF+ #*#...#*#, 79 total punctuation
// thus, it has #*#* or *#*# on any 32*19-bit boundary

fn aligned_part(buffer: &[u8]) -> (usize, &[u32]) {
    let mut sptr = buffer.as_ptr() as usize;
    let mut eptr = sptr + buffer.len();

    if sptr > !3 {
        // pointer into the last 32-bit word of the address space?  wat
        return (0, Default::default());
    }

    let offset = sptr.wrapping_neg() & 3;
    sptr += offset; // just checked this won't overflow
    eptr -= eptr & 3; // cannot overflow by construction

    unsafe { (offset, slice::from_raw_parts(sptr as *const u32, (eptr - sptr) / 4)) }
}

#[inline(never)]
pub fn find_chapter_header(mut buffer: &[u8]) -> Option<usize> {
    // returns something pointing at four consequtive puncts, guaranteed to
    // find if there is a run of 79
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

    fn is_real(buffer: &[u8], mut midp: usize) -> Option<usize> {
        // backtrack to the beginning of the line
        while midp > 0 && (buffer[midp] == b'#' || buffer[midp] == b'*') {
            midp -= 1;
        }

        // make sure we reached a CRLF
        if buffer[midp] != b'\r' && buffer[midp] != b'\n' {
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
        match hunt(buffer) {
            None => return None,
            Some(mix) => {
                match is_real(buffer, mix) {
                    Some(chap) => return Some(chap + offset),
                    None => {
                        buffer = &buffer[mix + 1..];
                        offset += mix + 1;
                    }
                }
            }
        }
    }
}

#[derive(Eq,PartialEq,Copy,Clone)]
pub struct LongStr<'a>(pub &'a [u8]);

impl<'a> Hash for LongStr<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.len().hash(state);
    }
}
