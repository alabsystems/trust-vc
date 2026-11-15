verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
proof fn lemma(i: int)
    ensures s(i) == s(1),
{
    assume(false);
}
proof fn t(b: bool, c: bool, x: int)
    requires
        (if x == 1 { b } else { x == 2 }),
{
    {
        lemma(x);
        assert(s(0) == 0);
        assert(s(2) == 3);
    }
}
}
