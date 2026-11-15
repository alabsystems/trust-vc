verus! {
uninterp spec fn p(i: int) -> bool;

proof fn t()
    requires forall|i: int| #[trigger] p(i),
{
    assert(p(3));
}
}
