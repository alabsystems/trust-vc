::verus_builtin_macros::verus!{
fn g() -> (r: u64)
    ensures r == 1
{
    let mut x: u64 = 0;
    proof { x = 1; }
    x
}
}
