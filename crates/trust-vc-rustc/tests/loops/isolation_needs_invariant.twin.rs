verus! {
fn f(x: u32)
    requires x == 5
{
    let mut i: u32 = 0;
    while i < 3
        invariant
            i <= 3,
            i <= 4,
        decreases 3 - i
    {
        assert(x == 5);
        i = i + 1;
    }
}
}
