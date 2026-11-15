::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { (|| { #[verifier::no_such_attribute] 1u64 })(); }
}
