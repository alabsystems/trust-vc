::verus_builtin_macros::verus!{
fn g() { let c = |x: u64| #[verifier::no_such_attribute] (x + 1); }
}
