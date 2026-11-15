verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
proof fn t(b: bool, c: bool, x: int, y: int)
    requires
        (if x == 1 { b } else { x == 2 }),
{
    assert((s(x) <= s(1)) ==> s(2) == 3) by { assert(s(0) == 0); };
}
}
