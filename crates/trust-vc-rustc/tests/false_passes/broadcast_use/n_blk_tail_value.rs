::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn f() -> bool { true }
fn test() -> (r: u64) ensures r == 1 { let u = { assert(true); broadcast use f; }; assert(f()); 1 }
}
