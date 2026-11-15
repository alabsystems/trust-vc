::verus_builtin_macros::verus!{
proof fn g(x: u64) {
    let tracked y = x;
}
}
