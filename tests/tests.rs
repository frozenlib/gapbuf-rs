#[macro_use]
extern crate gapbuf;

use gapbuf::GapBuffer;
use std::cell::RefCell;
use std::collections::HashSet;
use std::panic;
use std::panic::AssertUnwindSafe;

#[test]
fn new() {
    let buf = GapBuffer::<u32>::new();

    assert_eq!(buf.is_empty(), true);
    assert_eq!(buf.len(), 0);
    assert_eq!(buf.gap(), 0);
    assert_eq!(buf.capacity(), 0);
}
#[test]
fn with_capacity() {
    let buf = GapBuffer::<u32>::with_capacity(10);

    assert_eq!(buf.is_empty(), true);
    assert_eq!(buf.len(), 0);
    assert_eq!(buf.gap(), 0);
    assert!(buf.capacity() >= 10);
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
fn eq_gapbuf1() {
    let mut buf = GapBuffer::new();
    buf.push_back(1);

    assert_eq!(buf, gap_buffer![1]);
}

#[test]
fn eq_gapbuf2() {
    let mut buf = GapBuffer::new();
    buf.push_back(2);
    buf.push_back(8);

    assert_eq!(buf, gap_buffer![2, 8]);
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
fn isnert_before_gap() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);
    buf.set_gap(3);

    buf.insert(1, 9);
    assert_eq!(buf, [1, 9, 2, 3, 4]);
}

#[test]
fn isnert_before_gap_near() {
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
        for r in 0..2 {
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
fn insert_iter() {
    let mut b = gap_buffer![1, 2, 3, 4];
    b.insert_iter(2, vec![10, 11]);
    assert_eq!(b, [1, 2, 10, 11, 3, 4]);
}

#[test]
#[should_panic]
fn insert_iter_out_of_range() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.insert_iter(5, vec![1, 2]);
}

#[test]
fn insert_iter_each() {
    let e0 = vec![1, 2, 3, 4];
    let b0 = gap_buffer![1, 2, 3, 4];

    for i in 0..5 {
        let mut e1 = e0.clone();
        e1.insert(i, 10);
        e1.insert(i + 1, 11);
        for g in 0..5 {
            let mut b1 = b0.clone();
            b1.set_gap(g);
            b1.insert_iter(i, vec![10, 11]);
            assert_eq!(b1, e1);
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
    for g in 0..3 {
        let mut b = gap_buffer![0, 1, 2];
        b.set_gap(g);
        b.push_back(3);
        assert_eq!(b, [0, 1, 2, 3]);
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
    for g in 0..3 {
        let mut b = gap_buffer![0, 1, 2];
        b.set_gap(g);
        b.push_front(9);
        assert_eq!(b, [9, 0, 1, 2]);
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
    let mut buf = gap_buffer![1, 2, 3, 4, 5];
    buf.set_gap(5);
    let value = buf.swap_remove(0);
    assert_eq!(value, 1);
    assert_eq!(buf, [5, 2, 3, 4]);
}

#[test]
fn swap() {
    let e0 = vec![1, 2, 3, 4, 5];
    let b0 = gap_buffer![1, 2, 3, 4, 5];

    for i in 0..5 {
        for j in 0..5 {
            let mut e1 = e0.clone();
            let mut b1 = b0.clone();
            e1.swap(i, j);
            b1.swap(i, j);
            assert_eq!(b1, e1);
        }
    }
}

#[test]
#[should_panic]
fn index_out_of_range() {
    let mut buf = gap_buffer![1, 2, 3, 4];
    buf.reserve(10);
    buf[4];
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
        TestDrop {
            t: t,
            name: name,
            is_panic: is_panic,
        }
    }
}

impl<'a> Drop for TestDrop<'a> {
    fn drop(&mut self) {
        let mut t = self.t.borrow_mut();
        t.insert(self.name);
        if self.is_panic {
            panic!("in drop panic!");
        }
    }
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
fn zero_sized_type() {
    let mut buf = GapBuffer::new();
    buf.push_back(());
    buf.push_back(());

    assert_eq!((), buf[0]);
    assert_eq!((), buf[1]);
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
