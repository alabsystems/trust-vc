::verus_builtin_macros::verus!{
fn g(x: u64) -> (r: u64) ensures r == x { return #[verifier::proof_note("a")] #[verifier::proof_note("b")] x; }
}
