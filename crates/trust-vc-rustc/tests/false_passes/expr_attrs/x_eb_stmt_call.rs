::verus_builtin_macros::verus!{
fn e() {}
#[verifier::external_body]
fn f() { #[verifier::no_such_attribute] e(); }
}
