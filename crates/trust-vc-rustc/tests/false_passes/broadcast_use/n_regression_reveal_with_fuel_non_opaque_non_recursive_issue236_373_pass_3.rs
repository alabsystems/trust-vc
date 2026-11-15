::verus_builtin_macros::verus!{
spec fn is_true(a: bool) -> bool { a }

proof fn foo() {
    let _gv = { broadcast use is_true; };
}
}
