verus! {
fn t(mut p: u64) -> (r: u64)
    ensures r == p,
{
    loop
        decreases 1int,
    {
        break;
        p = 7;
    }
    p
}
}
