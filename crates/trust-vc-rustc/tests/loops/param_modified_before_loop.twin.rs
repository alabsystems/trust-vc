verus! {
fn f(mut a: u8) -> (r: u8)
    ensures r == a
{
    a = 7;
    loop
        invariant true
        decreases 0int
    {
        return a;
    }
}
}
