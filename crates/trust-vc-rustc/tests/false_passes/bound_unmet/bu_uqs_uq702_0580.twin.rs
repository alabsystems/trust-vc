verus!{
impl Q for A { }
pub trait U<T> {
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
pub mod m2 {
use crate::*;
impl Tr for A { }
}
impl U<Z> for B {
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub trait Q { }
pub mod m1 {
use crate::*;
impl Tr for B { }
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl U<B> for Z {
    proof fn lm0(&self) { }
}
impl U<A> for A {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
} // verus!
