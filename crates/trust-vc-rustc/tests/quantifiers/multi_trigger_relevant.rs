verus! {
uninterp spec fn p(i: int) -> bool;
uninterp spec fn q(i: int) -> bool;

proof fn t()
    requires forall|i: int, j: int| #[trigger] p(i) && #[trigger] q(j),
{
    assert(p(3) ==> q(4));
}
}
