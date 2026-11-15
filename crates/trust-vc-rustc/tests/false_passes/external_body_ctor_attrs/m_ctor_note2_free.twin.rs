::verus_builtin_macros::verus!{
pub struct S1(pub u8);
#[verifier::external_body]
fn f() { S1(1u8); }
fn user() { f(); }
}
