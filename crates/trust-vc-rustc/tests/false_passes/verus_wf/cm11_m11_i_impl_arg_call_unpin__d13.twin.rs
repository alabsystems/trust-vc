::verus_builtin_macros::verus!{
#[verifier::external]
pub struct C<const X: char>(pub u8);

pub struct WU<D: Sync>(pub D);
#[verifier::external]
pub struct WD<D: core::ops::Deref>(pub D);
pub trait Tr { }
pub trait Tr2<X> { }
pub trait Tm { fn m(&self) -> u8; }
pub trait Tm2<X> { fn m(&self) -> u8; }
impl Tm2<WU<u8>> for u16 { fn m(&self) -> u8 { 1 } }
fn user() { let x = <u16 as Tm2<WU<u8>>>::m(&1u16); }
}
