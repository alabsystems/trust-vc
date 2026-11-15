verus!{
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
pub trait Q: Tr { }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
pub proof fn fA() { (A { a: 0 }).lm0(); }
impl Tr for A { }
pub struct B { pub b: u8 }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl Q for A { }
}
impl Tr for B { }
} // verus!
