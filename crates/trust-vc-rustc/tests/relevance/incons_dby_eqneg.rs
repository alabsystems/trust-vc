verus! {
#[verifier::decreases_by]
proof fn f_dec(i: int) {
    assume(false);
}
spec fn f(i: int) -> bool
    decreases i
    via f_dec
{
    !f(i)
}
proof fn t() {
    assert(f(0) == !f(0));
}
}
