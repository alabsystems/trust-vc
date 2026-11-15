::verus_builtin_macros::verus!{
fn e(x: u64) { }
proof fn p(x: u64) { }
proof fn g(x: u64) {
    e(x);
}
}
