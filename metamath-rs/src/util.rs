//! Support functions that don't belong anywhere else or use unsafe code.

use fnv::FnvHasher;
use std::collections;
use std::hash::BuildHasherDefault;
use std::ptr;
use std::slice;

/// Type alias for hashmaps to allow swapping out the implementation.
pub(crate) type HashMap<K, V> = collections::HashMap<K, V, BuildHasherDefault<FnvHasher>>;
/// Type alias for hashsets to allow swapping out the implementation.
pub(crate) type HashSet<K> = collections::HashSet<K, BuildHasherDefault<FnvHasher>>;

/// Empty a vector of a POD type without checking each element for droppability.
pub(crate) fn fast_clear<T: Copy>(vec: &mut Vec<T>) {
    unsafe {
        vec.set_len(0);
    }
}

// emprically, *most* copies in the verifier where fast_extend and extend_from_within
// are used are 1-2 bytes
const unsafe fn short_copy<T>(src: *const T, dst: *mut T, count: usize) {
    match count {
        1 => ptr::write(dst, ptr::read(src)),
        2 => ptr::write(dst.cast::<[T; 2]>(), ptr::read(src.cast())),
        _ => ptr::copy_nonoverlapping(src, dst, count),
    }
}

/// Appends a POD slice to a vector with a simple `memcpy`.
pub(crate) fn fast_extend<T: Copy>(vec: &mut Vec<T>, other: &[T]) {
    vec.reserve(other.len());
    unsafe {
        let len = vec.len();
        short_copy(other.as_ptr(), vec.as_mut_ptr().add(len), other.len());
        vec.set_len(len + other.len());
    }
}

// Rust already assumes you're on a twos-complement byte-addressed pure-endian
// machine. A chapter header is CRLF+ $ ( CRLF+ #*#...#*#, 79 total punctuation.
// Thus, it has #*#* or *#*# on any 32*19-bit boundary

// find a maximal 4-byte aligned slice within a larger byte slice
fn aligned_part(buffer: &[u8]) -> (usize, &[u32]) {
    let mut s_ptr = buffer.as_ptr() as usize;
    let mut e_ptr = s_ptr + buffer.len();

    if buffer.len() < 4 {
        return (0, Default::default());
    }

    let offset = s_ptr.wrapping_neg() & 3;
    s_ptr += offset; // just checked this won't overflow
    e_ptr -= e_ptr & 3; // cannot overflow by construction

    unsafe {
        (
            offset,
            slice::from_raw_parts(s_ptr as *const u32, (e_ptr - s_ptr) / 4),
        )
    }
}

/// Search for a properly formatted set.mm-style chapter header in a byte
/// buffer, taking advantage of a known repetetive 79-byte substring with a
/// Boyer-Moore search.
///
/// This runs on the full file on every reload, but it's also pretty good at
/// running at full memory bandwidth.
#[inline(never)]
#[must_use]
pub(crate) fn find_chapter_header(mut buffer: &[u8]) -> Option<usize> {
    // returns something pointing at four consequtive puncts, guaranteed to find
    // if there is a run of 79
    fn hunt(buffer: &[u8]) -> Option<usize> {
        let (offset, aligned) = aligned_part(buffer);

        let mut pp = 0;
        while pp < aligned.len() {
            let word = aligned[pp];
            if word == u32::from_ne_bytes(*b"#*#*") || word == u32::from_ne_bytes(*b"*#*#") {
                return Some(offset + pp * 4);
            }
            pp += 19;
        }

        None
    }

    const LANDING_STRIP: &[u8] =
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
        if buffer.len() - midp < LANDING_STRIP.len() + 1
            || &buffer[midp + 1..midp + 1 + LANDING_STRIP.len()] != LANDING_STRIP
        {
            return None;
        }

        // skip CRLF
        while midp > 0 && (buffer[midp] == b'\r' || buffer[midp] == b'\n') {
            midp -= 1;
        }
        // make sure we reached [CRLF] $(
        if midp >= 2
            && buffer[midp] == b'('
            && buffer[midp - 1] == b'$'
            && (buffer[midp - 2] == b'\r' || buffer[midp - 2] == b'\n')
        {
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
            }
            buffer = &buffer[mix + 1..];
            offset += mix + 1;
        } else {
            return None;
        }
    }
}
