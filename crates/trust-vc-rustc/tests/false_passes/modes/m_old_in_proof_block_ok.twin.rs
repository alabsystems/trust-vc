::verus_builtin_macros::verus!{
fn g(x: &mut u64)
    ensures *x == *old(x)
{
    let y = *old(x);
}
}
