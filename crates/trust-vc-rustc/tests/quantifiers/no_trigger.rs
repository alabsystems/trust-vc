verus! {
uninterp spec fn p(i: int) -> bool;

proof fn t()
    requires forall|i: int| p(i) ==> i + 1 > i,
{
}
}
