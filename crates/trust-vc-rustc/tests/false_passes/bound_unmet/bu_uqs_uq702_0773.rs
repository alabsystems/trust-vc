verus!{
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
impl U for Z {
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq0(&self) { assert(self.mm() == 2); }
}
impl Q for B { }
pub mod m2 {
use crate::*;
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
}
pub struct B { pub b: u8 }
pub trait Tr { }
impl Tr for Z { }
impl Q for Z { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub trait Q { }
impl Tr for B { }
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
}
} // verus!
