verus! {
spec fn tr<A>(value: A) -> bool { true }
proof fn test(n: nat) {
    assert(tr::<nat>(n));
    assert(exists|i: nat| i >= 0 && tr(i));
}
}
