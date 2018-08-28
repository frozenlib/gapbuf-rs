#![feature(test)]

extern crate gapbuf;
extern crate test;
use gapbuf::GapBuffer;
use std::collections::VecDeque;
use test::Bencher;

#[bench]
fn push_back_vec(b: &mut Bencher) {
    b.iter(|| {
        let mut b = Vec::new();
        for n in 0..1000 {
            b.push(n)
        }
        b
    });
}
#[bench]
fn push_back_gapbuf(b: &mut Bencher) {
    b.iter(|| {
        let mut b = GapBuffer::new();
        for n in 0..1000 {
            b.push_back(n)
        }
        b
    });
}
#[bench]
fn push_back_vec_deque(b: &mut Bencher) {
    b.iter(|| {
        let mut b = VecDeque::new();
        for n in 0..1000 {
            b.push_back(n)
        }
        b
    });
}

#[bench]
fn push_front_vec(b: &mut Bencher) {
    b.iter(|| {
        let mut b = Vec::new();
        for n in 0..1000 {
            b.insert(0, n)
        }
        b
    });
}
#[bench]
fn push_front_gapbuf(b: &mut Bencher) {
    b.iter(|| {
        let mut b = GapBuffer::new();
        for n in 0..1000 {
            b.push_front(n)
        }
        b
    });
}
#[bench]
fn push_front_vec_deque(b: &mut Bencher) {
    b.iter(|| {
        let mut b = VecDeque::new();
        for n in 0..1000 {
            b.push_front(n)
        }
        b
    });
}
