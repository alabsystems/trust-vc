::verus_builtin_macros::verus!{
fn test() -> (r: u64) ensures r == 0 { let mut v: (u64, u64) = (0, 1); v.1 -= 1; v.1 }
}
