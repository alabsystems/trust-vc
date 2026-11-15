::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { (|x: u8| { no_unwind(); x }); }
fn user() {{ f(); }}
}
