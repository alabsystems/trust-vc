verus!{
impl U for A {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { assert(self.mm() == 2); }
}
pub trait Tr { }
pub mod m1 {
use crate::*;
impl Q for A { }
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
impl Tr for B { }
}
pub proof fn fB() { (B { b: 0 }).lm1(); }
pub trait Q { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
}
} // verus!
