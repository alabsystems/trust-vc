::verus_builtin_macros::verus!{
fn t() { let mut a: [u64; 2] = [0, 0]; (#[verifier::proof_note("m")] a)[0] = 5; }
}
