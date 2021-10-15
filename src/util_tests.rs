use crate::util;
use std::sync::Arc;

#[test]
fn test_ptr_eq() {
    let a1 = Arc::new("Hello, world".to_string());
    let a2 = a1.clone();
    assert!(!std::ptr::eq(&a1, &a2));
    assert!(Arc::ptr_eq(&a1, &a2));
}

#[test]
fn test_fast_clear() {
    let mut vec = vec![1u32, 2, 3, 4, 5];
    util::fast_clear(&mut vec);
    assert_eq!(vec.len(), 0);
    assert_eq!(vec.capacity(), 5);
}

#[test]
fn test_fast_extend() {
    let mut vec = vec![1u32, 2, 3];
    util::fast_extend(&mut vec, &[4, 5]);
    assert_eq!(vec, vec![1, 2, 3, 4, 5]);
    util::fast_extend(&mut vec, &[6]);
    assert_eq!(vec, vec![1, 2, 3, 4, 5, 6]);
}

#[test]
fn test_copy_portion() {
    let mut s = Vec::from(b"Hello world" as &[u8]);
    s.extend_from_within(2..4);
    assert_eq!(s, b"Hello worldll");
    s.extend_from_within(0..1);
    assert_eq!(s, b"Hello worldllH");
    s.extend_from_within(6..11);
    assert_eq!(s, b"Hello worldllHworld");
}

#[test]
#[should_panic(expected = "out of range")]
fn test_copy_portion_oob() {
    let mut s = Vec::from(b"Hello world" as &[u8]);
    s.extend_from_within(11..12);
}

#[test]
fn test_find_chapter() {
    assert_eq!(util::find_chapter_header(b""), None);
    assert_eq!(util::find_chapter_header(b"#*#*"), None);
    assert_eq!(
        util::find_chapter_header(
            b"Hello\n$(\n#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*\
        #*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#\n"
        ),
        Some(6)
    );
    assert_eq!(
        util::find_chapter_header(
            b"#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#\
        *#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#\nHello\n$(\n#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#\
        *#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#\n"
        ),
        Some(86)
    );
    assert_eq!(
        util::find_chapter_header(
            b"\n$(\n#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#\
        *#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#\n"
        ),
        Some(1)
    );
    assert_eq!(
        util::find_chapter_header(
            b"\r\n$(\r\n#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#\
        *#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#\n"
        ),
        Some(2)
    );
    assert_eq!(
        util::find_chapter_header(
            b"\n$(MOO\r\n#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*\
        #*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#\n"
        ),
        None
    );
    assert_eq!(
        util::find_chapter_header(
            b"\n$(\r\n#*#*#*#*#*#*#*#*#*#*#*###*#*#*#*#*#*#\
        *#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#\n"
        ),
        None
    );
}
