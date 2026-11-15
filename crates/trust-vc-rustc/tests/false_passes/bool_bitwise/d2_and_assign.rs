::verus_builtin_macros::verus!{
fn test(b: bool) -> (r: bool) ensures r == b { let mut x = true; x &= b; x }
}
