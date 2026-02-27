#![feature(test)]

extern crate test;

use self::test::Bencher;
use gap_buf::GapBuffer;
use std::collections::VecDeque;

#[bench]
fn push_back_vec(b: &mut Bencher) {
    b.iter(|| {
        let mut b = Vec::new();
        for n in 0..10000 {
            b.push(n)
        }
        b
    });
}
#[bench]
fn push_back_gapbuf(b: &mut Bencher) {
    b.iter(|| {
        let mut b = GapBuffer::new();
        for n in 0..10000 {
            b.push_back(n)
        }
        b
    });
}
#[bench]
fn push_back_deque(b: &mut Bencher) {
    b.iter(|| {
        let mut b = VecDeque::new();
        for n in 0..10000 {
            b.push_back(n)
        }
        b
    });
}

#[bench]
fn push_front_vec(b: &mut Bencher) {
    b.iter(|| {
        let mut b = Vec::new();
        for n in 0..10000 {
            b.insert(0, n)
        }
        b
    });
}
#[bench]
fn push_front_gapbuf(b: &mut Bencher) {
    b.iter(|| {
        let mut b = GapBuffer::new();
        for n in 0..10000 {
            b.push_front(n)
        }
        b
    });
}
#[bench]
fn push_front_deque(b: &mut Bencher) {
    b.iter(|| {
        let mut b = VecDeque::new();
        for n in 0..10000 {
            b.push_front(n)
        }
        b
    });
}

#[bench]
fn insert_mid_vec(b: &mut Bencher) {
    b.iter(|| {
        let mut b = Vec::new();
        for n in 0..10000 {
            let mid = b.len() / 2;
            b.insert(mid, n)
        }
        b
    });
}
#[bench]
fn insert_mid_gapbuf(b: &mut Bencher) {
    b.iter(|| {
        let mut b = GapBuffer::new();
        for n in 0..10000 {
            let mid = b.len() / 2;
            b.insert(mid, n)
        }
        b
    });
}
#[bench]
fn insert_mid_deque(b: &mut Bencher) {
    b.iter(|| {
        let mut b = VecDeque::new();
        for n in 0..10000 {
            let mid = b.len() / 2;
            b.insert(mid, n)
        }
        b
    });
}

#[bench]
fn collect_vec(b: &mut Bencher) {
    b.iter(|| {
        let b: Vec<_> = (0..10000).collect();
        b
    });
}
#[bench]
fn collect_gapbuf(b: &mut Bencher) {
    b.iter(|| {
        let b: GapBuffer<_> = (0..10000).collect();
        b
    });
}
#[bench]
fn collect_deque(b: &mut Bencher) {
    b.iter(|| {
        let b: VecDeque<_> = (0..10000).collect();
        b
    });
}

#[bench]
fn iter_vec(b: &mut Bencher) {
    let s: Vec<_> = (0..100000).collect();
    b.iter(|| {
        let s: usize = s.iter().sum();
        s
    });
}

#[bench]
fn iter_gapbuf(b: &mut Bencher) {
    let s: GapBuffer<_> = (0..100000).collect();
    b.iter(|| {
        let s: usize = s.iter().sum();
        s
    });
}

#[bench]
fn iter_deque(b: &mut Bencher) {
    let s: VecDeque<_> = (0..100000).collect();
    b.iter(|| {
        let s: usize = s.iter().sum();
        s
    });
}
