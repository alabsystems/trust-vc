verus!{
pub struct A { pub a: u8 }
pub trait Q { }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
impl Q for A { }
impl Q for B { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl Tr for B { }
pub struct Z { pub z: u8 }
pub mod m1 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
}
}
pub trait Tr { }
pub struct B { pub b: u8 }
} // verus!
