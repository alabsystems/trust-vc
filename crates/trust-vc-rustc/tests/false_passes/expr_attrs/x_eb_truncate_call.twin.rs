::verus_builtin_macros::verus!{
fn e() {}
#[verifier::external_body]
fn f() { e(); }
}
