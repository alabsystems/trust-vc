::verus_builtin_macros::verus!{
fn e(x: u64) {}
#[verifier::external_body]
fn f() { e(#[verifier::no_such_attribute] 1); }
}
