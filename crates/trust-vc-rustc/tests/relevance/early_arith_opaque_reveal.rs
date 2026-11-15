verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn k(n: int) -> int;
#[verifier::opaque]
spec fn v(i: int) -> bool { i + 1 == 2 }
spec fn w(i: int) -> bool { s(i) == s(1) }
proof fn t(x: int)
    requires
        v(x),
        k(1) > 0,
        w(x),
{
    reveal(v);
    assert(s(0) == 0);
    assert(s(2) == 3);
}
}
