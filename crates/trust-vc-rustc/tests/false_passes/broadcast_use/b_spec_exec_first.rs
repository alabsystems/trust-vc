::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn f() -> bool { true }
fn test() -> (r: u64) ensures f() { broadcast use f; 1 }
}
