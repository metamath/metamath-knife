//! Mini-library for an optimized `HashSet<usize>` which reduces to bit
//! operations for a small universe.
//!
//! The current implementation falls back to bit operations on a large dense
//! array, which would be problematic if sparse; however, this is used to
//! support the verifier, and will never see an index larger than ~40 on the
//! standard set.mm.  (Thus, on a 64-bit build the fallback code doesn't get
//! exercised at all without special measures.)

use std::ops::BitOrAssign;
use std::slice;


/// A set of variable indices.
#[derive(Default,Debug)]
pub struct Bitset {
    head: usize,
    tail: Option<Box<Vec<usize>>>,
}

fn bits_per_word() -> usize {
    usize::max_value().count_ones() as usize
}

#[inline(never)]
fn clone_slow(arg: &Box<Vec<usize>>) -> Box<Vec<usize>> {
    arg.clone()
}

impl Clone for Bitset {
    #[inline]
    fn clone(&self) -> Bitset {
        Bitset {
            head: self.head,
            tail: match self.tail {
                None => None,
                Some(ref tail) => Some(clone_slow(&tail)),
            },
        }
    }
}

impl Bitset {
    /// Creates a new empty `Bitset`.  Does not allocate.  Equivalent to
    /// `Bitset::default()`.
    pub fn new() -> Bitset {
        Bitset {
            head: 0,
            tail: None,
        }
    }

    fn tail(&self) -> &[usize] {
        match self.tail {
            None => Default::default(),
            Some(ref bx) => &bx,
        }
    }

    fn tail_mut(&mut self) -> &mut Vec<usize> {
        if self.tail.is_none() {
            self.tail = Some(Box::new(Vec::new()));
        }
        self.tail.as_mut().unwrap()
    }

    /// Adds a single bit to a set.
    pub fn set_bit(&mut self, bit: usize) {
        if bit < bits_per_word() {
            self.head |= 1 << bit;
        } else {
            let word = bit / bits_per_word() - 1;
            let tail = self.tail_mut();
            if word >= tail.len() {
                tail.resize(word + 1, 0);
            }
            tail[word] |= 1 << (bit & (bits_per_word() - 1));
        }
    }

    /// Tests a set for a specific bit.
    pub fn has_bit(&self, bit: usize) -> bool {
        if bit < bits_per_word() {
            (self.head & (1 << bit)) != 0
        } else {
            let word = bit / bits_per_word() - 1;
            let tail = self.tail();
            if word >= tail.len() {
                false
            } else {
                (tail[word] & (1 << (bit & (bits_per_word() - 1)))) != 0
            }
        }
    }
}

impl<'a> BitOrAssign<&'a Bitset> for Bitset {
    fn bitor_assign(&mut self, rhs: &'a Bitset) {
        self.head |= rhs.head;
        if !rhs.tail().is_empty() {
            let rtail = rhs.tail();
            let stail = self.tail_mut();
            if rtail.len() > stail.len() {
                stail.resize(rtail.len(), 0);
            }
            for i in 0..rtail.len() {
                stail[i] |= rtail[i];
            }
        }
    }
}

impl<'a> IntoIterator for &'a Bitset {
    type Item = usize;
    type IntoIter = BitsetIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        BitsetIter {
            bits: self.head,
            offset: 0,
            buffer: self.tail().iter(),
        }
    }
}

/// Iterator for set bits in a bitset.
pub struct BitsetIter<'a> {
    bits: usize,
    offset: usize,
    buffer: slice::Iter<'a, usize>,
}

impl<'a> Iterator for BitsetIter<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        while self.bits == 0 {
            self.offset += bits_per_word();
            match self.buffer.next() {
                Some(bits) => self.bits = *bits,
                None => return None,
            }
        }
        let tz = self.bits.trailing_zeros() as usize;
        self.bits &= self.bits - 1;
        Some(tz + self.offset)
    }
}
