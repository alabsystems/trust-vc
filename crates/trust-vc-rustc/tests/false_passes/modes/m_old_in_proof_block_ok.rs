::verus_builtin_macros::verus!{
fn g(x: &mut u64)
    ensures *x == *old(x)
{
    proof { let y = *old(x); }
}
}
