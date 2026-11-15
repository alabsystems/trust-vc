verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
proof fn t()
    requires s(0) == 0 && s(1) == 1,
{
    assert(s(2) == 3);
}
}
