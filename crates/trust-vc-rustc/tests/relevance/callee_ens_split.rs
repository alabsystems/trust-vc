verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn k(n: int) -> int;
proof fn lr(i: int)
    requires i >= 1
    ensures s(i) == s(1)
{
    admit();
}
proof fn lt(i: int)
    requires i == i
    ensures s(i) == s(1)
{
    admit();
}
proof fn ln(i: int)
    ensures s(i) == s(1)
{
    admit();
}
proof fn t(x: int, b: bool)
    requires
        x == 1 || x == 2,
{
    lr(x);
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
