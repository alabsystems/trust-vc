::verus_builtin_macros::verus!{
proof fn f(n: nat) {
    g(n);
}
proof fn g(n: nat) {
    assert(n >= 0);
}
}
