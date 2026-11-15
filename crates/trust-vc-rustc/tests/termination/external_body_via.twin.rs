verus! {
#[verifier::opaque]
spec fn f(i: int) -> int
    decreases i
    via f_decreases
{
    0
}

#[verifier::decreases_by]
proof fn f_decreases(i: int) {
}
}
