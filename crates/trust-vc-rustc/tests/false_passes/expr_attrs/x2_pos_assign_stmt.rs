::verus_builtin_macros::verus!{
fn g() { let mut x: u64 = 0; #[verifier::no_such_attribute] x = 5; }
}
