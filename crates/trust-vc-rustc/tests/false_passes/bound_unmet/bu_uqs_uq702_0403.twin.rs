verus!{
pub trait Q: Tr { } impl Tr for Z { } impl Q for Z { }
pub struct A { pub a: u8 }
pub mod m2 {
use crate::*;
impl Q for B { }
impl U<Z> for B {
    proof fn lm0(&self) { }
}
}
pub struct Z { pub z: u8 }
impl Tr for B { }
pub struct B { pub b: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
impl U<B> for A {
    proof fn lm0(&self) { }
}
pub trait Tr { }
} // verus!
