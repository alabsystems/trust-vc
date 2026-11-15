::verus_builtin_macros::verus!{
fn f(x: u64) requires x == 5 { assert(#[verifier::proof_note("a")] #[verifier::proof_note("b")] x == 5); }
}
