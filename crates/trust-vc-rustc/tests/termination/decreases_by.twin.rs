verus! {
uninterp spec fn one() -> int;

proof fn is_one()
    ensures one() == 1
{
    admit();
}

spec fn f(i: int) -> int
    decreases i
    via f_decreases
{
    if i <= 0 { 0 } else { 1 + f(i - one()) }
}

#[verifier::decreases_by]
proof fn f_decreases(i: int) {
    assert(true);
}
}
