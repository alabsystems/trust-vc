verus! {
fn f(n: u32) -> (r: u32)
    requires n <= 100
    ensures r == n
{
    let mut i: u32 = 0;
    while i < n
        invariant i <= n, n <= 100
        decreases n - i
    {
        i = i + 1;
    }
    i
}
}
