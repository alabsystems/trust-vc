verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn r(n: int, b: bool) -> bool
    decreases n
{
    if n <= 0 { true } else { (if s(1) > 7 { s(1) > 7 } else { !(s(1) > 7) }) && r(n - 1, b) }
}
proof fn t(b: bool)
    requires r(1, b),
{
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
