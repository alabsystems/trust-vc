verus! {
uninterp spec fn p(i: int) -> bool;

proof fn t()
    requires p(3),
{
    assert(exists|i: int| #[trigger] p(i) && i == 3);
}
}
