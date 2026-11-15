verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn w(i: int) -> bool { (if s(i) > 7 { 1int } else { 2int }) != 1 }
proof fn t(b: bool, c: bool, x: int, y: int)
    requires
        w(1),
{
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
