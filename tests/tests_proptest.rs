use gap_buf::GapBuffer;
use proptest::{collection::vec, prelude::*};
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
#[proptest]
fn range(
    #[strategy(0..10usize)] len: usize,
    #[strategy(0..2usize)] reserve: usize,
    #[strategy(0..=#len)] gap: usize,
    #[strategy(0..=#len)] begin: usize,
    #[strategy(#begin..=#len)] end: usize,
) {
    let mut b: GapBuffer<_> = (0..len).collect();
    b.reserve_exact(reserve);
    b.set_gap(gap);

    let e: Vec<_> = b.iter().cloned().skip(begin).take(end - begin).collect();
    prop_assert_eq!(b.range(begin..end), e);
}

#[proptest]
fn splice(
    #[strategy(0..10usize)] len: usize,
    #[strategy(0..=#len)] begin: usize,
    #[strategy(#begin..=#len)] end: usize,
    #[strategy(0..=#len)] gap: usize,
    #[strategy(0..2usize)] reserve: usize,
    #[strategy(0..10usize)] len_insert: usize,
) {
    let mut e: Vec<_> = (0..len).collect();
    let er: Vec<_> = e.splice(begin..end, 10..10 + len_insert).collect();

    let mut b: GapBuffer<_> = (0..len).collect();
    b.reserve(reserve);
    b.set_gap(gap);

    let br: Vec<_> = b.splice(begin..end, 10..10 + len_insert).collect();
    assert_eq!(br, er, "removed list");
    assert_eq!(b, e, "new list");
}
