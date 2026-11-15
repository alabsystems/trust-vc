verus!{
pub mod m1 {
use crate::*;
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
}
impl U for A {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
}
pub trait Tr { }
pub trait Q: Tr { }
impl Q for A { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct A { pub a: u8 }
impl Tr for A { }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
pub proof fn fA() { (A { a: 0 }).lm1(); }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
} // verus!
