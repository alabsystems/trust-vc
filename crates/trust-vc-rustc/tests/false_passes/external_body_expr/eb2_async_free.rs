::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { async { }; }
fn user() {{ f(); }}
}
