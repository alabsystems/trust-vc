::verus_builtin_macros::verus!{
fn test(p: &mut u64) requires *old(p) == 0 ensures *p == 6 { *p += { *p = 5; 1 }; }
}
