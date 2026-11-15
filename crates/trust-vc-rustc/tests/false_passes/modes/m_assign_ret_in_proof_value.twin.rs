::verus_builtin_macros::verus!{
fn g(b: bool) -> (r: u64)
    ensures r == 1
{
    let mut x: u64 = 0;
    if b { x = 1; } else { x = 1; }
    x
}
}
