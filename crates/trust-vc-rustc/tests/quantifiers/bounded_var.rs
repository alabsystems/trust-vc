verus! {
uninterp spec fn p(i: u8) -> bool;

proof fn t() {
    assert(forall|i: u8| #[trigger] p(i) ==> i < 256);
}
}
