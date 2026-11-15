::verus_builtin_macros::verus!{
fn f(x: u64) requires #[verifier::proof_note(r"n")] x > 0 { }
}
