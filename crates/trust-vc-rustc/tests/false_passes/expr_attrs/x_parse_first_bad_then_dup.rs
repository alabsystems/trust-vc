::verus_builtin_macros::verus!{
fn f(x: u64) -> (r: u64) requires x < 10 ensures r == x + 1 { let y = #[verifier::proof_note(r"a")] #[verifier::proof_note("b")] (x + 1); y }
}
