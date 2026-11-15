::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { let y = 1u8; (|x: u8| { recommends([x > 0]); x }); }
fn user() {{ f(); }}
}
