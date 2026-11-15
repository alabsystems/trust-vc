::verus_builtin_macros::verus!{
pub struct T<A>(pub A);
#[verifier::external]
fn g_u8() -> u8 { 1 }
pub struct S(pub u8);
impl S { #[verifier::external_body] fn f() { Self(#[verifier::truncate] g_u8()); } }
fn user() { S::f(); }
}
