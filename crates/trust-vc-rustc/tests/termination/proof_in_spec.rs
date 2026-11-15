verus! {
uninterp spec fn one() -> int;

proof fn is_one()
    ensures one() == 1
{
    admit();
}

spec fn f(i: int) -> int
    decreases i
{
    if i <= 0 {
        0
    } else {
        proof {
            is_one();
        }
        1 + f(i - one())
    }
}
}
