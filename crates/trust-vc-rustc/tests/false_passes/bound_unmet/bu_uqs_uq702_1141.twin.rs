verus!{
pub struct B { pub b: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2;
}
pub trait Tr { }
impl U for A {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub mod m2 {
use crate::*;
impl U for B {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
}
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl Q for B { }
pub trait Q: Tr { }
impl Tr for B { }
} // verus!
