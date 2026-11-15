::verus_builtin_macros::verus!{
fn g(x: u64, y: u64) -> (r: u64)
    ensures r == 1 || r == 2
{
    if x == y {
        1
    } else {
        2
    }
}
}
