verus!{
pub trait Q { }
pub mod m2 {
use crate::*;
impl Tr for B { }
}
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub proof fn fB() { (B { b: 0 }).lm1(); }
pub trait Tr { }
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
} // verus!
