verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn k(n: int) -> int;
spec fn w(i: int) -> bool { s(i) == s(1) }
proof fn t(x: int, c: bool)
    requires
        (if c { x + 1 } else { x + 2 }) == 3,
        c,
        k(1) > 0,
        w(x),
{
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
