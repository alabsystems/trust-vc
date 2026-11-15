::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn f() -> bool { true }
#[verifier::opaque] spec fn g() -> bool { true }
fn test() { reveal(f); reveal(g); assert(f() && g()); }
}
