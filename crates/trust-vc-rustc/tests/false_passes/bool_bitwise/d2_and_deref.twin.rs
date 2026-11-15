::verus_builtin_macros::verus!{
fn test(p: &mut bool, b: bool) ensures *p == (*old(p) && b) { *p = *p && b; }
}
