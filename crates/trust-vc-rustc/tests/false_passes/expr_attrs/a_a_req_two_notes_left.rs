::verus_builtin_macros::verus!{
fn f(x: u64) requires #[verifier::proof_note("a")] #[verifier::proof_note("b")] x > 0 { }
}
