::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { let c = || { #[verifier::no_such_attribute] 1u64 }; }
}
