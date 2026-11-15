verus! {
spec fn f(i: int) -> bool
    decreases i
{
    proof { assume(false); }
    !f(i)
}
spec fn w(i: int) -> bool { f(i) == f(1) }
proof fn t(b: bool, c: bool, x: int)
    requires
        (if x == 1 { 1int } else { x }) <= 1,
        w(x),
{
    assert(false);
}
}
