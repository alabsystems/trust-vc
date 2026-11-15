::verus_builtin_macros::verus!{
proof fn p(x: u64) -> bool { true }
spec fn s0(x: u64) -> bool { true }
spec fn s(x: u64) -> bool {
    p(x)
}
}
