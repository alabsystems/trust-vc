::verus_builtin_macros::verus!{
proof fn p(tracked x: u64) { }
proof fn g(x: u64) {
    p(x);
}
}
