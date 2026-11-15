::verus_builtin_macros::verus!{
fn e(x: u64) -> bool { true }
spec fn s(x: u64) -> bool { true }
fn g(x: u64)
    ensures
        s(x)
{
}
}
