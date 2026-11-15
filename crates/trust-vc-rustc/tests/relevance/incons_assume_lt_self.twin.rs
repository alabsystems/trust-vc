verus! {
spec fn f(i: int) -> int
    decreases i
{
    proof { assume(false); }
    f(i) + 1
}
proof fn t() {
    assert(f(0) > f(0) + 5);
}
}
