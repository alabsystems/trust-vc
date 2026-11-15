verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
spec fn k(n: int) -> int;
spec fn vq(i: int) -> bool;
spec fn rv(i: int) -> bool
    decreases i
{
    if i <= 1 { i == 1 } else { rv(i - 1) && false }
}
spec fn rv2(i: int) -> bool
    decreases i
{
    if i <= 0 { false } else { i == 1 }
}
spec fn rv3(i: int) -> bool
    decreases i
{
    if i <= 0 { false } else if i == 1 { true } else { rv3(i - 1) && false }
}
spec fn v(i: int) -> bool { i == 1 }
spec fn w(i: int) -> bool { s(i) == s(1) }
spec fn wk(i: int) -> bool { s(i) == s(k(1)) }
spec fn w0(i: int) -> bool { s(i) == s(0int + 1) }
fn t(x: u64, y: u64)
    requires

        k(y as int) > 0,
        y == 1,
        w(x as int),
{
    proof { assert(s(0) == 0); }
    proof { assert(s(2) == 3); }
}
}
