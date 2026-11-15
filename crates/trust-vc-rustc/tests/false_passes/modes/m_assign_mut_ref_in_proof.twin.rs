::verus_builtin_macros::verus!{
fn g(x: &mut u64)
    ensures *x == 1
{
    *x = 1;
}
}
