verus! {
uninterp spec fn p(i: int) -> bool;

proof fn t()
    requires p(4),
{
    assert(exists|i: int| #[trigger] p(i) && i == 3);
}
}
