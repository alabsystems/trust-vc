::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn f() -> bool { true }
fn test() { assert(true); broadcast use f; assert(f()); }
}
