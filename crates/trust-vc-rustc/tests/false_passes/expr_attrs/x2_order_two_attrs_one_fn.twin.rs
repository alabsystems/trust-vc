::verus_builtin_macros::verus!{
fn f() { let a = 1u64; let b = #[verifier::bogus_b] 2u64; }
}
