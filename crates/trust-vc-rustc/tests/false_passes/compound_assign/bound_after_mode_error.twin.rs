::verus_builtin_macros::verus!{
fn e() { }
fn test() { let mut v: (u64, u64) = (0, 0); v.0 += 1; e(); }
}
