::verus_builtin_macros::verus!{
fn t() { let ghost mut g: int = 0; proof { #[verifier::proof_note("m")] g = 5; } assert(g == 5); }
}
