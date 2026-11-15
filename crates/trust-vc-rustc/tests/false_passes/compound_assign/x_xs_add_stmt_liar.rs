::verus_builtin_macros::verus!{
fn test(b: bool) -> (r: u64) ensures r == 1 { let mut v: (u64, u64) = (0, 0); v.0 += 1; v.0 }
}
