verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
fn t(b: bool) {
    let mut i: u64 = 0;
    while i < 3
        invariant
            i <= 3,
            (if s(1) > 7 { 1int } else { 2int }) != 3,
        decreases 3 - i,
    {
        i = i + 1;
    }
    proof {
        assert(s(0) == 0);
        assert(s(2) == 3);
    }
}
}
