::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { let y = 1u8; async { }; }
fn user() {{ f(); }}
}
