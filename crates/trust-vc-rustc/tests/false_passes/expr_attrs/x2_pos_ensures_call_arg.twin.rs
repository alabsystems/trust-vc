::verus_builtin_macros::verus!{
spec fn s(x: int) -> int { x }
fn f(x: u64) -> (r: u64) ensures r == s(x as int) { x }
}
