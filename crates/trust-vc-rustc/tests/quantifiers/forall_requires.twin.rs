verus! {
uninterp spec fn p(i: int) -> bool;

proof fn t()
    requires exists|i: int| #[trigger] p(i),
{
    assert(p(3));
}
}
