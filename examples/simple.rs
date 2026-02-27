use gap_buf::gap_buffer;

fn main() {
    let mut b = gap_buffer![1, 2, 3];
    b.insert(1, 10);
    assert_eq!(b, [1, 10, 2, 3]);

    b.remove(2);
    assert_eq!(b, [1, 10, 3]);
}
