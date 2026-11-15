::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { 'a: { }; }
fn user() { f(); }
}
