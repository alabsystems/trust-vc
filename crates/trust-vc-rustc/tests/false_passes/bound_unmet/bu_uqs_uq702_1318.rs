verus!{
pub proof fn fA() { (A { a: 0 }).lm0(); }
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub mod m1 {
use crate::*;
impl Tr for A { }
}
pub trait Tr { }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
impl Q for A { }
impl U for A {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
} // verus!
