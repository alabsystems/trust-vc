::verus_builtin_macros::verus!{
fn g(x: &mut u64) requires *old(x) < 10 ensures *x == *old(x) + 1 { *x = (*x + 1); }
}
