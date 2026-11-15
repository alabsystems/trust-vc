::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn f(x: u64) -> bool { x == x }
fn test(x: u64) { reveal(f); assert(f(x)); }
}
