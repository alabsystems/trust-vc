verus! {
spec fn tr<A>(value: A) -> bool { true }
proof fn test() {
    assert(tr::<int>(300));
    assert(exists|i: nat| i >= 0 && tr(i)); // expected verification failure
}
}
