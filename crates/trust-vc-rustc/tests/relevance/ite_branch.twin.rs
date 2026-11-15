verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
proof fn t(c: bool) {
    let v = if c { s(1) } else { s(1) };
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
