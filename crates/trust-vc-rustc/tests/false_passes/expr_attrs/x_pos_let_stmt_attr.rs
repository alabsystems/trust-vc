::verus_builtin_macros::verus!{
fn g() { #[verifier::no_such_attribute] let y: u64 = 1; }
}
