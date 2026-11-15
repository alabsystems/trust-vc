verus! {
uninterp spec fn p(i: int) -> bool;
uninterp spec fn q(i: int) -> bool;

proof fn t()
    requires
        forall|i: int| #[trigger] p(i) ==> q(i),
        p(3),
{
    assert(q(3));
}
}
