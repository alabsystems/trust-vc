::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f(b: bool) { if b { #[verifier::no_such_attribute] (); } }
}
