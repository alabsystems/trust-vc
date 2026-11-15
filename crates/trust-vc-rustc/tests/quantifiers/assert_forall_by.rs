verus! {
uninterp spec fn p(i: int) -> bool;
uninterp spec fn q(i: int) -> bool;

proof fn lemma(i: int)
    requires p(i),
    ensures q(i),
{
    admit();
}

proof fn t()
    requires p(3),
{
    assert forall|i: int| p(i) implies #[trigger] q(i) by {
        lemma(i);
    }
    assert(q(3));
}
}
