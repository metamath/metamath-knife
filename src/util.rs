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
