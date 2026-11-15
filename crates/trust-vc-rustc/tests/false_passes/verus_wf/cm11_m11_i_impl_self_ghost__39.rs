::verus_builtin_macros::verus!{
#[verifier::external]
pub struct C<const X: char>(pub u8);
#[verifier::external]
pub struct WU<D: Unpin>(pub D);
#[verifier::external]
pub struct WD<D>(pub D);
pub trait Tr { }
pub trait Tr2<X> { }
pub trait Tm { fn m(&self) -> u8; }
impl Tr for WD<Ghost<u8>> { }
fn user() { }
}
