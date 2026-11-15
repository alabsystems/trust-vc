::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { let x = #[verifier::no_such_attribute] 5u64; }
}
