::verus_builtin_macros::verus!{
proof fn p(x: u64) -> bool { true }
spec fn s(x: u64) -> bool { true }
fn g(x: u64)
    requires
        s(x)
{
}
}
