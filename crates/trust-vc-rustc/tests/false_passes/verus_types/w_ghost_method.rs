::verus_builtin_macros::verus!{
#[verifier::external]
pub struct C<const X: char>(pub u8);
#[verifier::external]
pub struct WU<D: Unpin>(pub D);
#[verifier::external]
pub struct WD<D: core::ops::Deref>(pub D);
pub trait Tr<X> { }
impl<X> Tr<X> for u8 { }
pub struct S {}
impl S { fn f<A>(&self, a: A) where WD<Ghost<u8>>: Sized {} }
fn user(s: &S) { s.f(1u8); }
}
