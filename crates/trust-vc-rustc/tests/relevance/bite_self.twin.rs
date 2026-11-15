verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
proof fn t(b: bool)
    requires
        if s(1) > 7 { s(1) > 7 } else { s(1) <= 6 },
{
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
