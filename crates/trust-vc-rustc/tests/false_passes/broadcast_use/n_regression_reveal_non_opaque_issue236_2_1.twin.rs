::verus_builtin_macros::verus!{
spec fn is_true(a: bool) -> bool { a }

proof fn foo() {
    hide(is_true);
    reveal(is_true);
    assert(is_true(true));
}
}
