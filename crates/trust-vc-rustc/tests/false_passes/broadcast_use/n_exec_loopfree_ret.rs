::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn f() -> bool { true }
fn test(b: bool) -> (r: bool) ensures r == f() { broadcast use f; true }
}
