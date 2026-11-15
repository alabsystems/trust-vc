::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { no_method_body() }
fn user() { f(); }
}
