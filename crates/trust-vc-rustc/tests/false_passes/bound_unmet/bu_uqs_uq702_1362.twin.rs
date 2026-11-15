verus!{
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub mod m2 {
use crate::*;
impl Q for B { }
}
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub struct A { pub a: u8 }
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm1(); }
}
impl Tr for B { }
impl Q for A { }
} // verus!
