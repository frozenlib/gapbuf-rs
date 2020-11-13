use gapbuf::GapBuffer;
use proptest::collection::vec;
use proptest::prelude::*;
use test_strategy::{proptest, Arbitrary};

#[derive(Arbitrary, Clone, Copy, Debug)]
enum VecAction {
    Insert(#[strategy(0..100usize)] usize),
    Remove(#[strategy(0..100usize)] usize),
    SetGap(#[strategy(0..100usize)] usize),
}

#[proptest]
fn insert_remove(#[strategy(vec(any::<VecAction>(), 0..100))] actions: Vec<VecAction>) {
    use self::VecAction::*;

    let mut e = Vec::new();
    let mut a = GapBuffer::new();

    let mut value = 0;
    for action in actions {
        match action {
            Insert(idx) => {
                value += 1;
                let idx = idx % (e.len() + 1);
                e.insert(idx, value);
                a.insert(idx, value);
            }
            Remove(idx) => {
                if !e.is_empty() {
                    let idx = idx % e.len();
                    e.remove(idx);
                    a.remove(idx);
                }
            }
            SetGap(idx) => {
                let idx = idx % (e.len() + 1);
                a.set_gap(idx);
            }
        }
        assert_eq!(a, e);
    }
}
#[derive(Arbitrary, Debug)]
struct RangeArg {
    #[strategy(0..10usize)]
    len: usize,
    #[strategy(0..2usize)]
    reserve: usize,
    #[strategy(0..=#len)]
    gap: usize,
    #[strategy(0..=#len)]
    begin: usize,
    #[strategy(#begin..=#len)]
    end: usize,
}
#[proptest]
fn range(a: RangeArg) {
    let b: GapBuffer<_> = (0..a.len).collect();
    let mut b = b.clone();
    b.reserve_exact(a.reserve);
    b.set_gap(a.gap);

    let e: Vec<_> = b
        .iter()
        .cloned()
        .skip(a.begin)
        .take(a.end - a.begin)
        .collect();
    prop_assert_eq!(b.range(a.begin..a.end), e);
}

#[derive(Arbitrary, Debug)]
struct SpliceArg {
    #[strategy(0..10usize)]
    len: usize,
    #[strategy(0..=#len)]
    begin: usize,
    #[strategy(#begin..=#len)]
    end: usize,
    #[strategy(0..=#len)]
    gap: usize,
    #[strategy(0..2usize)]
    reserve: usize,
    #[strategy(0..10usize)]
    len_insert: usize,
}
#[proptest]
fn splice(a: SpliceArg) {
    let mut e: Vec<_> = (0..a.len).collect();
    let er: Vec<_> = e.splice(a.begin..a.end, 10..10 + a.len_insert).collect();

    let mut b: GapBuffer<_> = (0..a.len).collect();
    b.reserve(a.reserve);
    b.set_gap(a.gap);

    let br: Vec<_> = b.splice(a.begin..a.end, 10..10 + a.len_insert).collect();
    assert_eq!(br, er, "removed list");
    assert_eq!(b, e, "new list");
}
