::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn f(x: u64) -> bool { x == x }
fn test(x: u64) { broadcast use f; assert(f(x)); }
}
