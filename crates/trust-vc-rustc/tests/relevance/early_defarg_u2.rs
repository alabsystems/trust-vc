verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn k(n: int) -> int;
spec fn u2(i: int, j: int) -> int { j }
spec fn w(i: int) -> bool { s(i) == s(1) }
proof fn t(x: int)
    requires
        k(1) > 0,
        w(u2(x, 1)),
{
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
