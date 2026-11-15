verus! {
#[verifier::loop_isolation(false)]
fn t(a: bool, b: bool) -> (r: u64)
    ensures r == 2 || (a && b),
{
    let mut x: u64 = 0;
    loop
        decreases 1int,
    {
        if a {
            if b {
                x = 1;
                break;
            }
        }
        x = 2;
        break;
    }
    x
}
}
