::verus_builtin_macros::verus!{
fn test(b: bool) -> (r: bool) ensures r == b { let mut v: (bool, u64) = (true, 0); v.0 &= b; v.0 }
}
