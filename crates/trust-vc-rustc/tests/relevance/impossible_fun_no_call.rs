verus! {
spec fn impossible_fun() -> bool
    decreases 0int
    via f_decreases
{
    !impossible_fun()
}
#[verifier::decreases_by]
proof fn f_decreases() {

}
proof fn bad_lemma()
    ensures
        false,
{
    assert(impossible_fun() == !impossible_fun());
    assert(false);
}
}
