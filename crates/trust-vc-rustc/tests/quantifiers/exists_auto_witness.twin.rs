verus! {
spec fn tr(i: int) -> bool {
    true
}

proof fn t() {
    assert(true);
    assert(exists|i: int| 0 <= i && tr(i));
}
}
