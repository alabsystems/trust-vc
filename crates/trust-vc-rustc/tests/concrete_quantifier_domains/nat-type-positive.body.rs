verus! {
spec fn tr<A>(value: A) -> bool { true }
proof fn test() {
    assert(tr::<nat>(300));
    assert(exists|i: nat| i >= 0 && tr(i));
}
}
