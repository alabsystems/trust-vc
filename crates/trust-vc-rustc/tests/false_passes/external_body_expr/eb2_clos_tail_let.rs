::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { let y = 1u8; (|x: u8| { requires([x > 0]) }); }
fn user() {{ f(); }}
}
