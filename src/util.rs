use std::ptr;

pub fn ptr_eq<T>(x: &T, y: &T) -> bool {
    x as *const _ == y as *const _
}

// avoids dropping overhead

pub fn fast_clear<T: Copy>(vec: &mut Vec<T>) {
    unsafe {
        vec.set_len(0);
    }
}

pub fn fast_truncate<T: Copy>(vec: &mut Vec<T>, len: usize) {
    unsafe {
        if len > vec.len() {
            vec.set_len(0);
        }
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
