::verus_builtin_macros::verus!{
fn e() {}
fn g() { #[verifier::no_such_attribute] e(); }
}
