::verus_builtin_macros::verus!{
spec fn is_true(a: bool) -> bool { a }

proof fn foo() { broadcast use is_true;
    reveal_with_fuel(is_true, 1);
}
}
