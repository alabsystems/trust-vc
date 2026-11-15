::verus_builtin_macros::verus!{
spec fn s(x: u64) -> bool { x > 3 }
fn g(x: u64) -> (r: u64)
    ensures r >= 1
{
    if s(x) { 1 } else { 2 }
}
}
