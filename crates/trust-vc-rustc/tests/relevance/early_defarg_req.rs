verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn k(n: int) -> int;
spec fn u(i: int) -> int { i }
spec fn one() -> int { 1 }
spec fn v(i: int) -> bool { i == 1 }
spec fn w(i: int) -> bool { s(i) == s(1) }
spec fn wu(i: int) -> bool { s(u(i)) == s(1) }
proof fn t(x: int, y: int)
    requires
        x == 1,
        k(1) > 0,
        w(u(x)),
{
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
