//! Utilities for source-offset/line-number mapping.

use crate::util::HashMap;
use std::cmp::Ordering;
use std::convert::TryFrom;

const PAGE: usize = 256;

/// An object for efficient repeated byte offset to line conversions.
///
/// The first time a query is made for a given buffer, an index is constructed
/// storing the line number at 256 byte intervals in the file.  Subsequent
/// queries can reuse the index.
///
/// This is expected to be a very short-lived object.  If the line cache
/// outlives any of the buffers it has been queried against, and future buffers
/// receive the same address range, the line cache will return incorrect results
/// (but will not crash).
#[derive(Default, Debug)]
pub struct LineCache {
    map: HashMap<(usize, usize), Vec<u32>>,
}

#[inline(never)]
fn make_index(mut buf: &[u8]) -> Vec<u32> {
    assert!(buf.len() < u32::MAX as usize - 1);
    let mut out = Vec::with_capacity(buf.len() / PAGE + 1);
    out.push(0);
    let mut count = 0u32;

    // record the running total of newlines every PAGE bytes
    while buf.len() >= PAGE {
        let mut page = &buf[0..PAGE];
        buf = &buf[PAGE..];
        // use an i8 accumulator to maximize the effectiveness of vectorization.
        // do blocks of 128 because we don't want to overflow the i8.  count
        // down because all vector hardware supported by Rust generates fewer
        // instructions that way (the natural compare instructions produce 0 and
        // -1, not 0 and 1).
        #[allow(clippy::cast_sign_loss)]
        while page.len() >= 128 {
            let mut inner = 0i8;
            for &ch in &page[0..128] {
                inner += -i8::from(ch == b'\n');
            }
            page = &page[128..];
            count += u32::from((inner as u8).wrapping_neg());
        }
        out.push(count);
    }

    out
}

// find the lowest offset for which from_offset would give the target.
// Panics if line number out of range.
fn line_to_offset(buf: &[u8], index: &[u32], line: u32) -> usize {
    let page = index
        .binary_search_by(|&ll| {
            if ll < line {
                Ordering::Less
            } else {
                Ordering::Greater
            }
        })
        .expect_err("cannot match");
    // page*PAGE is the first page-aligned which is >= to the goal line, OR it
    // points at an incomplete end page
    if page == 0 {
        // page 0 always has lineno 0, so inserting before it is only possible
        // if line is 0 or negative
        assert!(line == 0, "line out of range");
        return 0;
    }
    // (page-1)*PAGE, then, is *not* >= to the goal line, but it's close to
    // either the goal line or EOF
    let mut at_lineno = index[page - 1];
    let mut at_pos = (page - 1) * PAGE;
    while at_lineno < line {
        assert!(at_pos < buf.len(), "line out of range");
        if buf[at_pos] == b'\n' {
            at_lineno += 1;
        }
        at_pos += 1;
    }

    at_pos
}

impl LineCache {
    fn get_index(&mut self, buf: &[u8]) -> &Vec<u32> {
        self.map
            .entry((buf.as_ptr() as usize, buf.len()))
            .or_insert_with(|| make_index(buf))
    }

    /// Map a line to a buffer index.  Panics if out of range.
    #[must_use]
    pub fn to_offset(&mut self, buf: &[u8], line: u32) -> usize {
        line_to_offset(buf, self.get_index(buf), line - 1)
    }

    /// Map a buffer index to a (line, column) pair.
    /// ## Panics
    /// Panics if the buffer is larger than 4GiB or if offset is out of range.
    #[must_use]
    pub fn from_offset(&mut self, buf: &[u8], offset: usize) -> (u32, u32) {
        let index = self.get_index(buf);
        // find a start point
        let mut lineno = index[offset / PAGE];
        // fine-tune
        for &ch in &buf[offset / PAGE * PAGE..offset] {
            if ch == b'\n' {
                lineno += 1;
            }
        }
        // now for the column
        let colno = offset - line_to_offset(buf, index, lineno);
        (lineno + 1, u32::try_from(colno).unwrap() + 1)
    }

    /// Find the offset just after the end of the line (usually the
    /// location of a '\n', unless we are at the end of the file).
    #[must_use]
    pub fn line_end(buf: &[u8], offset: usize) -> usize {
        for (pos, &ch) in buf.iter().enumerate().skip(offset) {
            if ch == b'\n' {
                return pos;
            }
        }
        buf.len()
    }
}
