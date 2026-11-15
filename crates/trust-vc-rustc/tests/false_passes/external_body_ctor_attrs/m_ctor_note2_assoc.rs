::verus_builtin_macros::verus!{
pub struct S1(pub u8);
pub struct S {}
impl S { #[verifier::external_body] fn f() { S1(#[verifier::proof_note("a")] #[verifier::proof_note("b")] 1u8); } }
fn user() { S::f(); }
}
