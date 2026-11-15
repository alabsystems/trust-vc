verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn k(n: int) -> int;
spec fn w(i: int) -> bool { s(i) == s(1) }
proof fn ln(i: int)
    ensures s(i) == s(1)
{
    admit();
}
proof fn lw(i: int)
    ensures w(i)
{
    admit();
}
proof fn t(x: int, b: bool)
    requires
        x == 1 || x == 2,
        k(1) > 0,
{
    assert(s(0) == 0);
    ln(x);
    assert(s(2) == 3);
}
}
