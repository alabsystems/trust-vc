::verus_builtin_macros::verus!{
fn f() { let y = #[verifier::bogus_a] 1u64; }
fn g() { let y = #[verifier::bogus_b] 1u64; }
}
