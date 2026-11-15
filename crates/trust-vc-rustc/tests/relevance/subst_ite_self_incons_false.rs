verus! {
spec fn f(i: int) -> bool
    decreases i
{
    proof { assume(false); }
    !f(i)
}
proof fn t(b: bool, c: bool, x: int, y: int)
    requires
        (if x == 1 { b } else { x == 1 }),
        f(x) == f(1),
{
    assert(false);
}
}
