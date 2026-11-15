::verus_builtin_macros::verus!{
fn f() -> (r: u64) ensures #[verifier::proof_note("n")] r == 5 { 5 }
}
