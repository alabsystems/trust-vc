verus!{
pub proof fn fZ() { (Z { z: 0 }).lm1(); }
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
impl Tr for B { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
pub trait Q { }
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
pub mod m1 {
use crate::*;
impl Q for B { }
impl Tr for Z { }
}
impl U for Z {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { assert(self.mm() == 2); }
}
pub struct Z { pub z: u8 }
impl Q for Z { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub trait Tr { }
} // verus!
