verus! {
spec fn f(i: int) -> bool
    decreases i
{
    proof { assume(false); }
    !f(i)
}
spec fn veq(i: int, j: int) -> bool { i == j }
spec fn wf2(i: int, j: int) -> bool { f(i) == f(j) }
proof fn t(x: int, y: int)
    requires

        wf2(x, y),
{
    assert(false);
}
}
