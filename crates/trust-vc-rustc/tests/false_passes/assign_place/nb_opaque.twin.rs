::verus_builtin_macros::verus!{
fn t() { let mut x: u64 = 0; #[verifier::opaque] x = 5; assert(x == 6); }
}
