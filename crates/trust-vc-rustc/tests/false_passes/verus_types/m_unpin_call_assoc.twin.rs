::verus_builtin_macros::verus!{
#[verifier::external]
pub struct WU<D: Unpin>(pub D);
#[verifier::external]
fn g_wu() -> WU<u8> { WU(1) }
pub struct S {}
impl S { #[verifier::external_body] fn f() { } }
fn user() { S::f(); }
}
