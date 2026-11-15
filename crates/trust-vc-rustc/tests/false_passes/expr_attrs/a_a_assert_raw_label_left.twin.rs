::verus_builtin_macros::verus!{
fn f(x: u64) requires x == 5 { assert(#[verifier::proof_note("n")] x == 5); }
}
