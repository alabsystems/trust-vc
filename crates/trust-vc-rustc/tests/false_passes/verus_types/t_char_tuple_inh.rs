::verus_builtin_macros::verus!{
pub struct T<A>(pub A);
#[verifier::external]
pub struct C<const X: char>(pub u8);
#[verifier::external]
pub struct WU<D: Unpin>(pub D);
#[verifier::external]
pub struct WC<D: Clone>(pub D);
#[verifier::external]
pub struct WM<D: core::ops::DerefMut>(pub D);
#[verifier::external]
fn g_u8() -> u8 { 1 }
#[verifier::external]
fn g_c() -> C<'a'> { C(0) }
#[verifier::external]
fn g_id<A>(a: A) -> A { a }
#[verifier::external]
fn g_wu() -> WU<u8> { WU(1) }
#[verifier::external]
fn g_wc<D: Clone>(d: D) -> WC<D> { WC(d) }
#[verifier::external]
fn g_wm() -> WM<Tracked<u8>> { unimplemented!() }
pub struct S {}
impl S { #[verifier::external_body] fn f(&self) { g_id((g_c(), 1u8)); } }
fn user(s: &S) { s.f(); }
}
