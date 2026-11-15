::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn f() -> bool { true }
fn test() { let u = { broadcast use f; }; assert(f()); }
}
