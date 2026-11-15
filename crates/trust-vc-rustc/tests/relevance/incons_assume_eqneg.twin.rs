verus! {
spec fn f(i: int) -> bool
    decreases i
{
    proof { assume(false); }
    !f(i)
}
proof fn t() {
    assert(f(0) == !f(0) || f(0));
}
}
