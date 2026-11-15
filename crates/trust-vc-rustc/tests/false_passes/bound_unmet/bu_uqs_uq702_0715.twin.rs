verus!{
pub trait Q: Tr { } impl Tr for Z { } impl Q for Z { }
pub struct B { pub b: u8 }
impl U for Z {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
impl Tr for A { }
pub mod m1 {
use crate::*;
impl Q for A { }
}
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq1(&self) { assert(self.mm() == 2); }
}
pub trait Tr { }
pub struct A { pub a: u8 }
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl Tr for B { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2;
}
impl U for A {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
} // verus!
