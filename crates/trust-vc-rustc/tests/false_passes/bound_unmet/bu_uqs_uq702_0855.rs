verus!{
pub mod m2 {
use crate::*;
impl Q for A { }
}
impl Tr for A { }
pub proof fn fA() { (A { a: 0 }).lm1(); }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub trait Tr { }
pub trait Q { }
impl U for B {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
pub struct Z { pub z: u8 }
impl Q for B { }
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { assert(self.mm() == 2); }
}
}
impl Tr for B { }
} // verus!
