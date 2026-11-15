::verus_builtin_macros::verus!{
fn t() { let mut x: u64 = 0; #[verifier::all_triggers] x = 5; assert(x == 5); }
}
