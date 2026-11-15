verus!{
impl Tr for B { }
pub struct B { pub b: u8 }
pub trait Q: Tr { }
impl U for Z {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
}
pub mod m1 {
use crate::*;
impl U for B {
    proof fn rq0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
}
}
impl U for A {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
pub proof fn fB() { (B { b: 0 }).lm1(); }
pub trait Tr { }
pub struct A { pub a: u8 }
} // verus!
