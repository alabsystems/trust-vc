verus! {
spec fn tr(i: int) -> bool {
    true
}

proof fn t() {
    assert(tr(300));
    assert(exists|i: int| 0 <= i && tr(i));
}
}
