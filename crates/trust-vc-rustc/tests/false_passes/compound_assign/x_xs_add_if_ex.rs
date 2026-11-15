::verus_builtin_macros::verus!{
fn test(b: bool) { let mut v: (u64, u64) = (0, 0); if b { v.0 += 1; } }
}
