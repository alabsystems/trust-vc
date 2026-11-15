verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn k(n: int) -> int;
spec fn v(i: int) -> bool { i == 1 }
proof fn lv(i: int)
    requires v(i)
    ensures s(i) == s(1)
{
    admit();
}
proof fn t(x: int)
    requires
        v(x),
        k(1) > 0,
{
    lv(x);
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
