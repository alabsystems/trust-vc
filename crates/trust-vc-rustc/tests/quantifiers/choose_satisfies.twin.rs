verus! {
uninterp spec fn p(i: int) -> bool;
uninterp spec fn q(i: int) -> bool;

proof fn t()
    requires exists|i: int| #[trigger] q(i),
{
    let c = choose|i: int| p(i);
    assert(p(c));
}
}
