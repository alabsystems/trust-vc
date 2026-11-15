verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn u(n: int) -> int { n }
spec fn k(n: int) -> int;
spec fn v(i: int) -> bool { i == 1 }
spec fn v2(i: int) -> bool { i >= 1 && i <= 1 }
spec fn v3(i: int) -> bool { 1 == i }
spec fn w(i: int) -> bool { s(i) == s(1) }
spec fn w2(i: int) -> bool { s(1) == s(i) }
spec fn w3(i: int) -> bool { s(i) <= s(1) && s(1) <= s(i) }
proof fn t(x: int, y: int)
    requires

        k(1) > 0,
        w(x),
{
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
