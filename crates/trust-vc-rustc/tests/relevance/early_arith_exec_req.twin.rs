verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn k(n: int) -> int;
spec fn w(i: int) -> bool { s(i) == s(1) }
fn t(x: u64)
    requires
        x + 1 == x + 1,
        k(1) > 0,
        w(x as int),
{
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
