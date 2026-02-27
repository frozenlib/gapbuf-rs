use gap_buf::{gap_buffer, GapBuffer};
use std::cell::RefCell;
use std::collections::HashSet;
use std::panic;
use std::panic::AssertUnwindSafe;

#[test]
fn new() {
    let buf = GapBuffer::<u32>::new();

    assert!(buf.is_empty());
    assert_eq!(buf.len(), 0);
    assert_eq!(buf.gap(), 0);
    assert_eq!(buf.capacity(), 0);
}
#[test]
fn with_capacity() {
    let buf = GapBuffer::<u32>::with_capacity(10);

    assert!(buf.is_empty());
    assert_eq!(buf.len(), 0);
    assert_eq!(buf.gap(), 0);
    assert!(buf.capacity() >= 10);
}

#[test]
fn reserve() {
    let mut buf = GapBuffer::<u32>::new();
    buf.reserve(4);

    assert!(buf.capacity() >= 4);
    assert_eq!(buf.len(), 0);
}

#[test]
fn reserve_push_back() {
    let mut buf = GapBuffer::new();
    buf.reserve(4);
    buf.push_back(8);

    assert_eq!(buf.len(), 1);
    assert_eq!(buf[0], 8);
}

#[test]
fn push_back_reserve() {
    let mut buf = GapBuffer::new();
    buf.push_back(8);

    buf.reserve(4);
    assert_eq!(buf.len(), 1);
    assert_eq!(buf[0], 8);
    assert!(buf.capacity() >= 5);
}

#[test]
fn reserve_exact() {
    let mut buf = GapBuffer::<u32>::new();
    buf.reserve_exact(4);

    assert!(buf.capacity() >= 4);
    assert_eq!(buf.len(), 0);
}

#[test]
fn reserve_exact_push_back() {
    let mut buf = GapBuffer::new();
    buf.reserve_exact(4);
    buf.push_back(8);

    assert_eq!(buf.len(), 1);
    assert_eq!(buf[0], 8);
}

#[test]
fn push_back_reserve_exact() {
    let mut buf = GapBuffer::new();
    buf.push_back(8);

    buf.reserve_exact(4);
    assert_eq!(buf.len(), 1);
    assert_eq!(buf[0], 8);
    assert!(buf.capacity() >= 5);
}

#[test]
fn shrink_to_fit_0() {
    let mut buf: GapBuffer<u32> = GapBuffer::new();
    buf.reserve(10);
    buf.shrink_to_fit();

    assert_eq!(buf.capacity(), 0);
}

#[test]
fn shrink_to_fit_1() {
    let mut buf = GapBuffer::new();
    buf.push_back(1);
    buf.reserve(10);
    buf.shrink_to_fit();

    assert_eq!(buf.capacity(), 1);
    assert_eq!(buf, [1]);
}

#[test]
fn shrink_to_fit_gap_head() {
    let mut buf = GapBuffer::new();
    buf.push_back(1);
    buf.reserve(10);
    buf.set_gap(0);
    buf.shrink_to_fit();

    assert_eq!(buf.capacity(), 1);
    assert_eq!(buf, [1]);
}
#[test]
fn shrink_to_fit_gap_mid() {
    let mut buf = gap_buffer![1, 2];
    buf.reserve(10);
    buf.set_gap(1);
    buf.shrink_to_fit();

    assert_eq!(buf.capacity(), 2);
    assert_eq!(buf, [1, 2]);
}

#[test]
fn set_gap_to_head() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);

    buf.set_gap(0);
    assert_eq!(buf.gap(), 0);
    assert_eq!(buf, [1, 2, 3, 4]);
}

#[test]
fn set_gap_to_tail() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);

    buf.set_gap(4);
    assert_eq!(buf.gap(), 4);
    assert_eq!(buf, [1, 2, 3, 4]);
}

#[test]
fn set_gap_many() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    assert_eq!(buf, [1, 2, 3, 4]);

    buf.reserve(10);
    assert_eq!(buf, [1, 2, 3, 4]);

    let mut gaps = Vec::new();

    for n in [0, 1, 2, 3, 4, 3, 2, 1, 0, 2, 4, 2, 0].iter() {
        let gap = *n;
        gaps.push(gap);
        buf.set_gap(gap);
        assert_eq!(buf.gap(), gap, "gaps: {:?}", &gaps);
        assert_eq!(buf, [1, 2, 3, 4]);
    }
}
#[test]
#[should_panic]
fn set_gap_out_of_range() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);

    assert_eq!(buf, [1, 2, 3, 4]);
    buf.set_gap(5);
}

#[test]
fn set_gap_each() {
    let buf0 = gap_buffer![1, 2, 3, 4];

    for i in 0..5 {
        for j in 0..5 {
            let mut buf1 = buf0.clone();
            buf1.set_gap(i);
            buf1.set_gap(j);
            assert_eq!(buf1, buf0);
        }
    }
}

#[test]
fn insert_before_gap() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);
    buf.set_gap(3);

    buf.insert(1, 9);
    assert_eq!(buf, [1, 9, 2, 3, 4]);
}

#[test]
fn insert_before_gap_near() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);
    buf.set_gap(3);

    buf.insert(2, 9);
    assert_eq!(buf, [1, 2, 9, 3, 4]);
}

#[test]
fn insert_after_gap() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);
    buf.set_gap(1);

    buf.insert(3, 9);
    assert_eq!(buf, [1, 2, 3, 9, 4]);
}
#[test]
fn insert_after_gap_near() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);
    buf.set_gap(1);

    buf.insert(2, 9);
    assert_eq!(buf, [1, 2, 9, 3, 4]);
}

#[test]
fn insert_at_gap() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);
    buf.set_gap(1);

    buf.insert(1, 9);
    assert_eq!(buf, [1, 9, 2, 3, 4]);
}

#[test]
#[should_panic]
fn insert_out_of_range() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.insert(5, 9);
}

#[test]
fn insert_each() {
    let e0 = vec![1, 2, 3, 4];
    let b0 = gap_buffer![1, 2, 3, 4];

    for i in 0..5 {
        let mut e1 = e0.clone();
        e1.insert(i, 5);
        for r in 0..3 {
            for g in 0..5 {
                let mut b1 = b0.clone();
                b1.reserve_exact(r);
                b1.set_gap(g);
                b1.insert(i, 5);
                assert_eq!(b1, e1);
            }
        }
    }
}

#[test]
fn insert_many() {
    let mut b = gap_buffer![1, 2, 3, 4];
    b.insert_many(2, vec![10, 11]);
    assert_eq!(b, [1, 2, 10, 11, 3, 4]);
}

#[test]
#[should_panic]
fn insert_many_overflow() {
    let mut b = gap_buffer![1, 2, 3, 4];
    b.insert_many(0, std::iter::repeat(0));
}

#[test]
#[should_panic]
fn insert_many_out_of_range() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.insert_many(5, vec![1, 2]);
}

#[test]
fn insert_many_each() {
    let e0 = vec![1, 2, 3, 4];
    let b0 = gap_buffer![1, 2, 3, 4];

    for r in 0..3 {
        for i in 0..5 {
            let mut e1 = e0.clone();
            e1.insert(i, 10);
            e1.insert(i + 1, 11);
            for g in 0..5 {
                let mut b1 = b0.clone();
                b1.reserve_exact(r);
                b1.set_gap(g);
                b1.insert_many(i, vec![10, 11]);
                assert_eq!(b1, e1);
            }
        }
    }
}

#[test]
fn push_back1() {
    let mut buf = GapBuffer::new();
    buf.push_back(9);

    assert_eq!(buf.len(), 1);
    assert_eq!(buf[0], 9);
}

#[test]
fn push_back2() {
    let mut buf = GapBuffer::new();
    buf.push_back(9);
    buf.push_back(12);

    assert_eq!(buf.len(), 2);
    assert_eq!(buf[0], 9);
    assert_eq!(buf[1], 12);
}

#[test]
fn push_back_each() {
    for r in 0..3 {
        for g in 0..3 {
            let mut b = gap_buffer![0, 1, 2];
            b.reserve_exact(r);
            b.set_gap(g);
            b.push_back(3);
            assert_eq!(b, [0, 1, 2, 3]);
        }
    }
}

#[test]
fn push_front1() {
    let mut buf = GapBuffer::new();
    buf.push_front(9);

    assert_eq!(buf.len(), 1);
    assert_eq!(buf[0], 9);
}

#[test]
fn push_front2() {
    let mut buf = GapBuffer::new();
    buf.push_front(9);
    buf.push_front(12);

    assert_eq!(buf.len(), 2);
    assert_eq!(buf[0], 12);
    assert_eq!(buf[1], 9);
}

#[test]
fn push_front_each() {
    for r in 0..3 {
        for g in 0..3 {
            let mut b = gap_buffer![0, 1, 2];
            b.reserve_exact(r);
            b.set_gap(g);
            b.push_front(9);
            assert_eq!(b, [9, 0, 1, 2]);
        }
    }
}

#[test]
fn remove_before_gap() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);
    buf.set_gap(2);
    buf.remove(0);
    assert_eq!(buf, [2, 3, 4]);
}

#[test]
fn remove_before_gap_near() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);
    buf.set_gap(2);
    buf.remove(1);
    assert_eq!(buf, [1, 3, 4]);
}

#[test]
fn remove_after_gap() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);
    buf.set_gap(2);
    buf.remove(3);
    assert_eq!(buf, [1, 2, 3]);
}
#[test]
fn remove_after_gap_near() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);
    buf.set_gap(2);
    buf.remove(2);
    assert_eq!(buf, [1, 2, 4]);
}

#[test]
#[should_panic]
fn remove_out_of_range() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);
    buf.remove(4);
}

#[test]
fn swap_remove() {
    let e0 = vec![1, 2, 3, 4, 5];
    let b0 = gap_buffer![1, 2, 3, 4, 5];
    for i in 0..5 {
        let mut e1 = e0.clone();
        e1.remove(i);

        for r in 0..3 {
            for g in 0..6 {
                let mut b1 = b0.clone();
                b1.reserve_exact(r);
                b1.set_gap(g);
                b1.swap_remove(i);

                let mut b1: Vec<_> = b1.into_iter().collect();
                b1.sort_unstable();
                assert_eq!(b1, e1);
            }
        }
    }
}

#[test]
fn swap() {
    let e0 = vec![1, 2, 3, 4, 5];
    let b0 = gap_buffer![1, 2, 3, 4, 5];

    for i in 0..5 {
        for j in 0..5 {
            let mut e1 = e0.clone();
            let mut b1 = b0.clone();
            b1.reserve(2);
            e1.swap(i, j);
            b1.swap(i, j);
            assert_eq!(b1, e1);
        }
    }
}

#[test]
fn clear() {
    for r in 0..3 {
        for g in 0..5 {
            let mut b = gap_buffer![1, 2, 3, 4];
            b.reserve_exact(r);
            b.set_gap(g);
            b.clear();
            assert!(b.is_empty());
        }
    }
}

#[test]
fn truncate_t_is_not_copy() {
    for l in 0..4 {
        for t in 0..=l {
            let e: Vec<_> = (0..l).map(|x| x.to_string()).collect();
            let b: GapBuffer<_> = (0..l).map(|x| x.to_string()).collect();

            for r in 0..3 {
                for g in 0..=l {
                    let mut e = e.clone();
                    let mut b = b.clone();

                    b.reserve_exact(r);
                    b.set_gap(g);
                    b.truncate(t);
                    e.truncate(t);
                    assert_eq!(b, e, "l = {l}, t = {t}, r = {r}, g = {g}");
                }
            }
        }
    }
}

#[test]
fn truncate_t_is_copy() {
    for l in 0..4 {
        for t in 0..=l {
            let e: Vec<_> = (0..l).collect();
            let b: GapBuffer<_> = (0..l).collect();

            for r in 0..3 {
                for g in 0..=l {
                    let mut e = e.clone();
                    let mut b = b.clone();

                    b.reserve_exact(r);
                    b.set_gap(g);
                    b.truncate(t);
                    e.truncate(t);
                    assert_eq!(b, e, "l = {l}, t = {t}, r = {r}, g = {g}");
                }
            }
        }
    }
}

#[test]
fn retain() {
    let mut b = gap_buffer![1, 2, 3, 4];
    b.retain(|&x| x % 2 == 0);
    assert_eq!(b, [2, 4]);
}

#[test]
fn pop_front() {
    let b = gap_buffer![1, 2, 3];
    for g in 0..3 {
        let mut b = b.clone();
        b.set_gap(g);
        assert_eq!(b.pop_front(), Some(1));
        assert_eq!(b, [2, 3]);
    }
}

#[test]
fn pop_back() {
    let b = gap_buffer![1, 2, 3];
    for g in 0..3 {
        let mut b = b.clone();
        b.set_gap(g);
        assert_eq!(b.pop_back(), Some(3));
        assert_eq!(b, [1, 2]);
    }
}

#[test]
fn drain() {
    let b = gap_buffer![1, 2, 3, 4];
    for g in 0..5 {
        let mut b = b.clone();
        b.set_gap(g);
        let d: Vec<_> = b.drain(1..3).collect();
        assert_eq!(d, [2, 3]);
        assert_eq!(b, [1, 4]);

        b.drain(..);
        assert!(b.is_empty());
    }
}

#[test]
fn splice() {
    for len in 0..5 {
        for len_insert in 0..3 {
            for begin in 0..=len {
                for end in begin..=len {
                    let mut e: Vec<_> = (0..len).collect();
                    let er: Vec<_> = e.splice(begin..end, 10..10 + len_insert).collect();
                    for g in 0..=len {
                        for r in 0..2 {
                            let mut b: GapBuffer<_> = (0..len).collect();
                            b.reserve(r);
                            b.set_gap(g);

                            let br: Vec<_> = b.splice(begin..end, 10..10 + len_insert).collect();

                            assert_eq!(br, er, "removed list");
                            assert_eq!(b, e, "new list");
                        }
                    }
                }
            }
        }
    }
}

struct TestDrop<'a> {
    t: &'a RefCell<HashSet<&'a str>>,
    name: &'a str,
    is_panic: bool,
}

impl<'a> TestDrop<'a> {
    fn new(t: &'a RefCell<HashSet<&'a str>>, name: &'a str) -> TestDrop<'a> {
        Self::new_with_panic(t, name, false)
    }
    fn new_with_panic(
        t: &'a RefCell<HashSet<&'a str>>,
        name: &'a str,
        is_panic: bool,
    ) -> TestDrop<'a> {
        TestDrop { t, name, is_panic }
    }
}

impl Drop for TestDrop<'_> {
    fn drop(&mut self) {
        let mut t = self.t.borrow_mut();
        t.insert(self.name);
        if self.is_panic {
            panic!("in drop panic!");
        }
    }
}

#[test]
fn impl_sync() {
    fn f(_: impl Sync) {}
    let buf = GapBuffer::<usize>::new();
    f(buf);
}

#[test]
fn impl_send() {
    fn f(_: impl Send) {}
    let buf = GapBuffer::<usize>::new();
    f(buf);
}

#[test]
fn drop() {
    let t = RefCell::new(HashSet::new());
    {
        let mut buf = GapBuffer::new();
        buf.push_back(TestDrop::new(&t, "A"));
    }
    let mut e = HashSet::new();
    e.insert("A");
    assert_eq!(*t.borrow_mut(), e);
}

#[test]
fn drop_all() {
    let t = RefCell::new(HashSet::new());
    {
        let mut buf = GapBuffer::new();
        buf.push_back(TestDrop::new(&t, "A"));
        buf.push_back(TestDrop::new(&t, "B"));
    }
    let mut e = HashSet::new();
    e.insert("A");
    e.insert("B");
    assert_eq!(*t.borrow_mut(), e);
}

#[test]
fn drop_all_on_panic1() {
    let t = RefCell::new(HashSet::new());
    let r = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut buf = GapBuffer::new();
        buf.push_back(TestDrop::new_with_panic(&t, "A", false));
        buf.push_back(TestDrop::new_with_panic(&t, "B", true));
    }));
    let mut e = HashSet::new();
    e.insert("A");
    e.insert("B");
    assert_eq!(*t.borrow_mut(), e);
    assert!(r.is_err());
}

#[test]
fn drop_all_on_panic2() {
    let t = RefCell::new(HashSet::new());
    let r = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut buf = GapBuffer::new();
        buf.push_back(TestDrop::new_with_panic(&t, "A", true));
        buf.push_back(TestDrop::new_with_panic(&t, "B", false));
    }));
    let mut e = HashSet::new();
    e.insert("A");
    e.insert("B");
    assert_eq!(*t.borrow_mut(), e);
    assert!(r.is_err());
}

#[test]
fn eq_slice1() {
    let mut buf = GapBuffer::new();
    buf.push_back(1);

    assert_eq!(buf, [1]);
}

#[test]
fn eq_slice2() {
    let mut buf = GapBuffer::new();
    buf.push_back(2);
    buf.push_back(8);

    assert_eq!(buf, [2, 8]);
}

#[test]
fn eq_gap_buf1() {
    let mut buf = GapBuffer::new();
    buf.push_back(1);

    assert_eq!(buf, gap_buffer![1]);
}

#[test]
fn eq_gap_buf2() {
    let mut buf = GapBuffer::new();
    buf.push_back(2);
    buf.push_back(8);

    assert_eq!(buf, gap_buffer![2, 8]);
}

#[test]
fn ord() {
    use std::cmp::Ordering::*;
    assert!(gap_buffer![1] < [2]);
    assert!(gap_buffer![2] > [1]);
    assert_eq!(gap_buffer![1].partial_cmp(&[1]), Some(Equal));

    assert!(gap_buffer![1, 1] > [1]);
    assert!(gap_buffer![1] < [1, 1]);

    assert!(gap_buffer![2, 1] > [1, 1]);
    assert!(gap_buffer![1, 1] < [2, 1]);

    assert!(gap_buffer![2, 1] > [1, 2]);
    assert!(gap_buffer![1, 2] < [2, 1]);
}

#[test]
fn iter() {
    for r in 0..2 {
        for g in 0..5 {
            let mut b = gap_buffer![1, 2, 3, 4];
            b.reserve_exact(r);
            b.set_gap(g);

            let mut i = b.iter();
            assert_eq!(i.next(), Some(&1));
            assert_eq!(i.next(), Some(&2));
            assert_eq!(i.next(), Some(&3));
            assert_eq!(i.next(), Some(&4));
            assert_eq!(i.next(), None);
        }
    }
}

#[test]
fn range() {
    let b = gap_buffer![1, 2, 3, 4, 5];
    for r in 0..2 {
        for g in 0..=b.len() {
            let mut b = b.clone();
            b.reserve_exact(r);
            b.set_gap(g);

            for begin in 0..=b.len() {
                for end in begin..=b.len() {
                    let e: Vec<_> = b.iter().cloned().skip(begin).take(end - begin).collect();
                    assert_eq!(b.range(begin..end), e);
                }
            }
        }
    }
}
#[test]
#[should_panic]
#[allow(clippy::reversed_empty_ranges)]
fn range_bad() {
    let b = gap_buffer![1, 2];
    b.range(2..1);
}

#[test]
#[should_panic]
fn range_begin_out_of_range() {
    let b = gap_buffer![1, 2];
    b.range(3..4);
}

#[test]
fn index() {
    for r in 0..2 {
        for g in 0..5 {
            let mut b = gap_buffer![1, 2, 3, 4];
            b.reserve_exact(r);
            b.set_gap(g);

            assert_eq!(b[0], 1);
            assert_eq!(b[1], 2);
            assert_eq!(b[2], 3);
            assert_eq!(b[3], 4);
        }
    }
}

#[test]
#[should_panic]
fn index_out_of_range() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);
    let _ = buf[4];
}

#[test]
fn get() {
    let b = gap_buffer![1, 2, 3, 4, 5];
    let v = [1, 2, 3, 4, 5];
    for r in 0..2 {
        for g in 0..5 {
            let mut b = b.clone();
            b.reserve_exact(r);
            b.set_gap(g);
            for i in 0..7 {
                assert_eq!(b.get(i), v.get(i));
            }
        }
    }
}

#[test]
fn get_mut() {
    let mut b = gap_buffer![1, 2, 3, 4, 5];
    *b.get_mut(2).unwrap() = 9;
    assert_eq!(b, [1, 2, 9, 4, 5]);
}

#[test]
fn covariant() {
    let mut b: GapBuffer<&'static str> = GapBuffer::new();
    b.push_back("aaa");
    let s = String::from("bbb");

    // `&GapBuffer<&static str>` can convert `&GapBuffer<&a>`
    fn c_gap_buf<'a>(_buf: &GapBuffer<&'a str>, _s: &'a str) {}
    c_gap_buf(&b, &s);

    // `Range<'b, &'static str>` can convert  `Range<'b, &'a str>`
    fn c_range<'a>(_buf: gap_buf::Range<&'a str>, _s: &'a str) {}
    c_range(b.range(0..1), &s);

    // `Range<'b, &'static str>` can not convert  `Range<'b, &'a str>`
    // fn c_range_mut<'a, 'b>(_buf: gap_buf::RangeMut<'b, &'a str>, _s: &'a str) {}
    // c_range_mut(b.range_mut(0..1), &s);

    // `&Slice<&static str>` can convert `&Slice<&a>`
    fn c_slice<'a>(_buf: &gap_buf::Slice<&'a str>, _s: &'a str) {}
    c_slice(&b, &s);

    // `&mut Slice<&static str>` can not convert `&mut Slice<&a>`
    // fn c_mut_slice<'a>(_buf: &mut gap_buf::Slice<&'a str>, _s: &'a str) {}
    // c_mut_slice(&mut b, &s);
}

#[test]
fn from_iter() {
    let buf: GapBuffer<_> = vec![8, 12, 9].into_iter().collect();

    assert_eq!(buf.len(), 3);
    assert_eq!(buf[0], 8);
    assert_eq!(buf[1], 12);
    assert_eq!(buf[2], 9);
}

#[test]
#[allow(clippy::unit_cmp)]
fn zero_sized_type() {
    let mut buf = GapBuffer::new();
    buf.push_back(());
    buf.push_back(());

    assert_eq!((), buf[0]);
    assert_eq!((), buf[1]);
}
