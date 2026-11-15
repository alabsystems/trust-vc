::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { (|#[verifier::proof] x: u8| x); }
fn user() {{ f(); }}
}
