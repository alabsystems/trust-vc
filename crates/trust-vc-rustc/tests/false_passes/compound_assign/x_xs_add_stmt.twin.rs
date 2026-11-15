::verus_builtin_macros::verus!{
fn test(b: bool) { let mut v: (u64, u64) = (0, 0); v.0 = v.0 + 1; }
}
