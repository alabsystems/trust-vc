::verus_builtin_macros::verus!{
#[verifier::external]
pub struct C<const X: char>(pub u8);
#[verifier::external]
fn g_c() -> C<'a'> { C(0) }
pub struct S {}
impl S { #[verifier::external_body] fn f() { } }
fn user() { S::f(); }
}
