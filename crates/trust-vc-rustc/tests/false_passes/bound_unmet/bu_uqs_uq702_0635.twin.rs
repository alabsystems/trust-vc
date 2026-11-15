verus!{
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Q for B { }
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl Q for A { }
impl U<B> for B {
    proof fn lm0(&self) { }
}
}
pub struct A { pub a: u8 }
impl U<A> for A {
    proof fn lm0(&self) { }
}
pub trait Q { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
}
} // verus!
