verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn k(n: int) -> int;
spec fn v(i: int) -> bool { i == 1 }
fn lv(i: u64)

    ensures s(i as int) == s(1)
{
    assume(false);
}
fn t(x: u64)
    requires
        v(x as int),
        k(1) > 0,
{
    lv(x);
    proof { assert(s(0) == 0); }
    proof { assert(s(2) == 3); }
}
}
