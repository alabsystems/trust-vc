verus! {
uninterp spec fn p(i: int) -> bool;

proof fn t() {
    let i1 = choose|i: int| p(i) && (1 + 1 == 2);
    let i2 = choose|i: int| (2 + 2 == 4) && p(i);
    assert(i1 == i2);
}
}
