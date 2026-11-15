::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn f() -> bool { true }
fn e() { }
fn test() { reveal(f); broadcast use f; }
}
