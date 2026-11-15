verus! {
spec fn f(i: int) -> bool
    decreases i
{
    !f(i)
}
proof fn t() {
    assert(f(0) == !f(0) || f(0));
}
}
