verus!{
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2;
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl U for B {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
pub struct Z { pub z: u8 }
pub mod m1 {
use crate::*;
impl Tr for B { }
}
impl U for Z {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
pub mod m2 {
use crate::*;
impl Q for Z { }
impl Tr for Z { }
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait Q: Tr { }
} // verus!
