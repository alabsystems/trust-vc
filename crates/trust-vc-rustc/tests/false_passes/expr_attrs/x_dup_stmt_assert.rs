::verus_builtin_macros::verus!{
fn g(x: u64) requires x == 1 { #[verifier::proof_note("a")] #[verifier::proof_note("b")] assert(x == 1); }
}
