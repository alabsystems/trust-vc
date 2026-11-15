verus!{
pub mod m1 {
use crate::*;
impl Q for A { }
}
impl U for B {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
pub trait Tr { }
impl Q for B { }
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct Z { pub z: u8 }
impl U for A {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
pub trait Q { }
impl Tr for B { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
} // verus!
