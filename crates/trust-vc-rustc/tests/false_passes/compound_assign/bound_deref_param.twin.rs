::verus_builtin_macros::verus!{
fn test(p: &mut u64) requires *old(p) < 10 ensures *p == *old(p) + 2 { *p += 1; }
}
