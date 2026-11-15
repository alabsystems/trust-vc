::verus_builtin_macros::verus!{
#[verifier::external]
fn g_u8() -> u8 { 1 }
pub struct S {}
impl S { #[verifier::external_body] fn f(&self) { let x: u8 = 1; #[verus::internal(header_unwrap_parameter)] let y: u8 = x; } }
fn user(s: &S) { s.f(); }
}
