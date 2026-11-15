verus! {
uninterp spec fn p(i: int) -> bool;

proof fn t()
    requires forall|i: int| i >= 0 ==> i + 1 > i,
{
}
}
