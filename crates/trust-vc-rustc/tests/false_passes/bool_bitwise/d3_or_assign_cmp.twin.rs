::verus_builtin_macros::verus!{
fn test(x: u64) -> (r: bool) ensures r == (x > 0) { let mut b: bool = false; b = b || x > 0; b }
}
