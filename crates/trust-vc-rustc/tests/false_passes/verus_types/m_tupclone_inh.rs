::verus_builtin_macros::verus!{
pub struct S {}
impl S { #[verifier::external_body] fn f(&self) { { <(u8, u8) as Clone>::clone }; } }
fn user(s: &S) { s.f(); }
}
