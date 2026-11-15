::verus_builtin_macros::verus!{
pub struct S1(pub u8);
pub struct S {}
impl S { #[verifier::external_body] fn f(&self) { S1(1u8); } }
fn user(s: &S) { s.f(); }
}
