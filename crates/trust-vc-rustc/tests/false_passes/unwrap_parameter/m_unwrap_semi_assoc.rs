::verus_builtin_macros::verus!{
#[verifier::external]
fn g_u8() -> u8 { 1 }
pub struct S {}
impl S { #[verifier::external_body] fn f() { #[verus::internal(header_unwrap_parameter)] g_u8(); } }
fn user() { S::f(); }
}
