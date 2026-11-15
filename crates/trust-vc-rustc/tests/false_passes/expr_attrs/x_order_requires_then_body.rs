::verus_builtin_macros::verus!{
fn f(x: u64) requires #[verifier::bogus_a] x > 0 { let y = #[verifier::bogus_b] (x + 1); }
}
