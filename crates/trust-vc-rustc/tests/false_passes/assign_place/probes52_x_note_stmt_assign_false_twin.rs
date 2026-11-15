::verus_builtin_macros::verus!{
fn t() { let mut y: u64 = 0; #[verifier::proof_note("m")] y = 1; assert(y == 1); }
}
