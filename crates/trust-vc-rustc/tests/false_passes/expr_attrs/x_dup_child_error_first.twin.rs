::verus_builtin_macros::verus!{
fn f() -> (r: u64) ensures #[verifier::proof_note("a")] #[verifier::proof_note("b")] (r == 5) { 5 }
}
