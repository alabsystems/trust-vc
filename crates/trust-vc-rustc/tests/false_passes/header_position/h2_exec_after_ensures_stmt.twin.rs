::verus_builtin_macros::verus!{
spec fn is_true(a: bool) -> bool { a }
fn foo() ensures true { hide(is_true); proof { } }
}
