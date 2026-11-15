::verus_builtin_macros::verus!{
pub struct T<A>(pub A);
#[verifier::external]
fn g_u8() -> u8 { 1 }
pub struct S(pub u8);
impl S { #[verifier::external_body] fn f() { T(#[verifier::proof_note("a")] #[verifier::custom_err("b")] 1u8); } }
fn user() { S::f(); }
}
