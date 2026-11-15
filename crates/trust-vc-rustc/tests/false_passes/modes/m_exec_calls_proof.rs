::verus_builtin_macros::verus!{
proof fn p(x: u64) { }
fn g(x: u64) {
    p(x);
}
}
