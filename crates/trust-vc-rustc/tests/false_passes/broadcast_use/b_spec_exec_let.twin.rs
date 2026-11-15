::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn f() -> bool { true }
fn test() { let u = { reveal(f); }; assert(f()); }
}
