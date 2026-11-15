verus! {
uninterp spec fn probe(i: int) -> bool;
spec fn keep<A>(value: A) -> bool { true }
proof fn test() {
    assume(forall|i: nat| #[trigger] probe(i as int) ==> !keep::<nat>(i));
    assume(probe(-1));
    assert(false); // expected verification failure
}
}
