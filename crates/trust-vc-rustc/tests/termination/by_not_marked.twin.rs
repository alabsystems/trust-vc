verus! {
spec fn f(i: int) -> int
    decreases i
    via f_decreases
{
    if i <= 0 { 0 } else { 1 + f(i - 1) }
}

#[verifier::decreases_by] proof fn f_decreases(i: int) {
}
}
