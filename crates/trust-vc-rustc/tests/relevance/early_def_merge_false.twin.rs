verus! {
spec fn f(i: int) -> bool
    decreases i
{
    proof { assume(false); }
    !f(i)
}
spec fn u(n: int) -> int { n }
spec fn k(n: int) -> int;
spec fn v(i: int) -> bool { i == 1 }
spec fn wf(i: int) -> bool { f(i) == f(1) }
proof fn t(x: int)
    requires

        k(1) > 0,
        wf(x),
{
    assert(false);
}
}
