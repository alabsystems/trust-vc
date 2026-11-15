verus! {
spec fn f(i: int) -> bool
    decreases i
{
    proof { assume(false); }
    !f(i)
}
proof fn t(b: bool, c: bool, x: int, y: int)
    requires
        (if f(1) { 1int } else { 2int }) != 1,
{
    assert(false);
}
}
