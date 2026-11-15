::verus_builtin_macros::verus!{
fn g() { let mut i: u64 = 0; while #[verifier::no_such_attribute] (i < 3) invariant i <= 3 decreases 3 - i { i = i + 1; } }
}
