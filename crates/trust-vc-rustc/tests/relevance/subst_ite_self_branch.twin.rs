verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
proof fn t(b: bool, c: bool, x: int)
    requires
        (if x == 1 { b } else { x == 2 }),
        s(x) == s(1),
{
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
