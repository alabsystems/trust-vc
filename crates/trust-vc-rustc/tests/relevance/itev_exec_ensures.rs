verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
fn l(b: bool)
    ensures (if s(1) > 7 { 1int } else { 2int }) != 3,
{
    assume(false);
}
fn t(b: bool) {
    l(b);
    proof {
        assert(s(0) == 0);
        assert(s(2) == 3);
    }
}
}
