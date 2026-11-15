::verus_builtin_macros::verus!{
fn test(p: &mut u64) requires *old(p) == 0 { *p = *p - { *p = 10; 1 }; }
}
