verus!{
pub proof fn fA() { (A { a: 0 }).lm0(); }
impl Q for A { }
impl U for A {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub trait Q { }
pub mod m1 {
use crate::*;
impl Q for B { }
}
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
impl Tr for A { }
pub trait Tr { }
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
} // verus!
