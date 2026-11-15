::verus_builtin_macros::verus!{

fn t() { let mut x: u64 = 0; #[verifier::proof_note("m")] x = 5; assert(x == 6); }
}
