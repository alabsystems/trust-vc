::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn p() { #[verifier::no_such_attribute] (); }
}
