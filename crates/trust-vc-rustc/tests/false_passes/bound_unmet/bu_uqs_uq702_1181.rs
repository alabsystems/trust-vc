verus!{
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2;
}
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
}
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq1(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { assert(self.mm() == 2); }
}
impl Q for B { }
impl Q for A { }
pub struct Z { pub z: u8 }
impl Tr for B { }
pub trait Q { }
pub struct A { pub a: u8 }
pub trait Tr { }
} // verus!
