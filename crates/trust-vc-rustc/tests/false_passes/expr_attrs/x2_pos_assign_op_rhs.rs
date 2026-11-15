::verus_builtin_macros::verus!{
fn g() { let mut x: u64 = 0; x += #[verifier::no_such_attribute] 1; }
}
