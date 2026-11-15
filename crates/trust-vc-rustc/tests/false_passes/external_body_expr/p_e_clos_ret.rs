::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { (|x: u8| { returns(x); x }); }
fn user() { f(); }
}
