verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn u(n: int) -> int { n }
spec fn k(n: int) -> int;
spec fn v(i: int) -> bool { i == 1 }
spec fn v0(i: int) -> bool { v(i) }
spec fn veq(i: int, j: int) -> bool { i == j }
spec fn rv(i: int) -> bool
    decreases i
{
    if i <= 1 { i == 1 } else { rv(i - 1) && false }
}
spec fn w(i: int) -> bool { s(i) == s(1) }
spec fn ww(i: int, j: int) -> bool { s(i) == s(j) }
spec fn wn(i: int) -> bool { w(i) }
proof fn l(i: int)
    ensures s(i) == s(1)
{
    admit();
}
proof fn lv(i: int)
    ensures v(i)
{
    admit();
}
proof fn t(x: int, y: int)
    requires
        u(x) == 1,
        k(1) > 0,
        w(x),
{
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
