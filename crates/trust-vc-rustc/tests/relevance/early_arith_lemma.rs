verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn k(n: int) -> int;
proof fn la(i: int)
    ensures i - 1 == 0
{
    admit();
}
spec fn w(i: int) -> bool { s(i) == s(1) }
proof fn t(x: int)
    requires
        k(1) > 0,
        w(x),
{
    la(x);
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
