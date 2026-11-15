::verus_builtin_macros::verus!{
pub struct T<A>(pub A);
#[verifier::external]
fn g_u8() -> u8 { 1 }
pub trait Tr { fn f(&self); }
pub struct S(pub u8);
impl Tr for S { #[verifier::external_body] fn f(&self) { Self(1u8); } }
fn user(s: &S) { s.f(); }
}
