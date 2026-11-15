verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
proof fn l(i: int) -> (r: int)
    ensures r == s(i),
{
    s(i)
}
proof fn t() {
    l(1);
    l(1);
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
