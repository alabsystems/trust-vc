::verus_builtin_macros::verus!{
pub struct S1(pub u8);
#[verifier::external]
fn g_u8() -> u8 { 1 }
pub struct S {}
impl S { #[verifier::external_body] fn f() { S1({ #[verifier::bogus] g_u8(); 1u8 }); } }
fn user() { S::f(); }
}
