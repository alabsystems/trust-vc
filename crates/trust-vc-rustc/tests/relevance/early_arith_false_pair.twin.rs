verus! {
spec fn f(i: int) -> bool
    decreases i
{
    proof { assume(false); }
    !f(i)
}
spec fn wf2(i: int, j: int) -> bool { f(i) == f(j) }
proof fn t(x: int, y: int)
    requires
        x + 1 == 2,
        y - 1 == 1,
        wf2(x, y),
{
    assert(false);
}
}
