verus!{
pub mod m2 {
use crate::*;
impl U<A> for B {
    proof fn lm0(&self) { }
}
}
pub struct B { pub b: u8 }
impl U<B> for A {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
pub struct Z { pub z: u8 }
impl Tr for A { }
impl Q for B { }
pub trait Q { }
pub trait Tr { }
} // verus!
