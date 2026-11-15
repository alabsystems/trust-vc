::verus_builtin_macros::verus!{
fn e(x: u64) -> bool { true }
spec fn s0(x: u64) -> bool { true }
spec fn s(x: u64) -> bool {
    e(x)
}
}
