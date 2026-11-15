verus! {
uninterp spec fn p(i: int) -> bool;
uninterp spec fn q(i: int) -> bool;

proof fn t()
    requires forall|i: int| #[trigger] q(i) && p(i),
{
    assert(q(3));
}
}
