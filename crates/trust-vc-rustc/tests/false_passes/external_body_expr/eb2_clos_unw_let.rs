::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { let y = 1u8; (|x: u8| { no_unwind(); x }); }
fn user() {{ f(); }}
}
