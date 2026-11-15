::verus_builtin_macros::verus!{
spec fn s(a: bool) -> bool { a }
fn foo() { hide(s); }
}
