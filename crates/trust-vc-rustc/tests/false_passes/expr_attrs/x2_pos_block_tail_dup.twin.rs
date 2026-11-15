::verus_builtin_macros::verus!{
fn f() -> (r: u64) ensures r == 1 { #[verifier::proof_note("a")] 1 }
}
