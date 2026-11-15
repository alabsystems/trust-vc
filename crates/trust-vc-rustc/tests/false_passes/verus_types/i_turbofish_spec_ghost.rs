::verus_builtin_macros::verus!{
#[verifier::external]
pub struct C<const X: char>(pub u8);
#[verifier::external]
pub struct WU<D: Unpin>(pub D);
#[verifier::external]
pub struct WD<D: core::ops::Deref>(pub D);
pub trait Tr { }
pub trait Tr2<X> { }
pub trait Tm { fn m(&self) -> u8; }
spec fn id<A>(a: u8) -> u8 { a }
proof fn user() { assert(id::<WD<Ghost<u8>>>(1) == 1); }
}
