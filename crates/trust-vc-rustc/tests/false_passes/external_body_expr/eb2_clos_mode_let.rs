::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { let y = 1u8; (|#[verifier::proof] x: u8| x); }
fn user() {{ f(); }}
}
