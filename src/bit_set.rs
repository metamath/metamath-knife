use std::ops::BitOrAssign;
use std::slice;

#[derive(Clone,Default,Debug)]
pub struct Bitset {
    head: usize,
    tail: Option<Box<Vec<usize>>>,
}

fn bits_per_word() -> usize {
    usize::max_value().count_ones() as usize
}

impl Bitset {
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
