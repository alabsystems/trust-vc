::verus_builtin_macros::verus!{
spec fn is_true(a: bool) -> bool { a }

fn foo() {
    reveal_with_fuel(is_true, 0);
}
}
