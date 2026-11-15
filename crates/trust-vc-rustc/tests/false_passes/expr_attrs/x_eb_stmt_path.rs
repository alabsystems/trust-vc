::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f(x: u64) { #[verifier::no_such_attribute] x; }
}
