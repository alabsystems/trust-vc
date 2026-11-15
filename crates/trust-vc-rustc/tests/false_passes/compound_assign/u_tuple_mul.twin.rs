::verus_builtin_macros::verus!{
fn test() -> (r: u64) ensures r == 6 { let mut v: (u64, u64) = (2, 0); v.0 = v.0 * 3; v.0 }
}
