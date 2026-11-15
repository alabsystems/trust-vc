::verus_builtin_macros::verus!{
pub struct T<A>(pub A);
pub struct T2<A, B>(pub A, pub B);
#[verifier::external]
pub struct C<const X: char>(pub u8);
#[verifier::external]
pub struct K<const X: u8>(pub u8);
#[verifier::external]
pub struct W<D: core::ops::Deref>(pub D);
#[verifier::external]
fn g_u8() -> u8 { 1 }
#[verifier::external]
fn g_c() -> C<'a'> { C(0) }
#[verifier::external]
fn g_k() -> K<3> { K(0) }
#[verifier::external]
fn g_id<A>(a: A) -> A { a }
#[verifier::external]
fn g_w() -> W<Box<u8>> { W(Box::new(1)) }
#[verifier::external]
fn g_wg() -> W<Ghost<u8>> { unimplemented!() }
pub trait Tr { #[verifier::external_body] fn f(&self) { Some(1u8); } }
pub struct S {}
impl Tr for S {}
fn user(s: &S) {{ s.f(); }}
}
