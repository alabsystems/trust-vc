::verus_builtin_macros::verus!{
#[verifier::external]
pub struct C<const X: char>(pub u8);
#[verifier::external]
pub struct WU<D: Unpin>(pub D);
#[verifier::external]
pub struct WD<D: core::ops::Deref>(pub D);
pub trait Tr<X> { }
impl<X> Tr<X> for u8 { }
fn f<A>(a: A) where A: Tr<C<'a'>> {}
fn user() { f(1u8); assert(false); }
}
