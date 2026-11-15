::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() -> (r: u64) ensures #[verifier::no_such_attribute] r == 5 { 5 }
}
