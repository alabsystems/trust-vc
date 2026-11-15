verus!{
pub mod m1 {
use crate::*;
impl Tr for B { }
}
pub struct A { pub a: u8 }
impl Q for A { }
impl Tr for A { }
pub mod m2 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
}
pub struct Z { pub z: u8 }
pub proof fn fA() { (A { a: 0 }).lm1(); }
pub trait Q: Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Tr { }
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for Z { }
} // verus!
