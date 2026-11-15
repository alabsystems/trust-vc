::verus_builtin_macros::verus!{
spec fn is_true(a: bool) -> bool { a }

proof fn foo() { reveal_with_fuel(is_true, 0u32);
    hide(is_true);
    reveal(is_true);
    assert(is_true(true));
}
}
