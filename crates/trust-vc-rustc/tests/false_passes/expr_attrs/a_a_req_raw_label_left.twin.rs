::verus_builtin_macros::verus!{
fn f(x: u64) requires #[verifier::proof_note("n")] x > 0 { }
}
