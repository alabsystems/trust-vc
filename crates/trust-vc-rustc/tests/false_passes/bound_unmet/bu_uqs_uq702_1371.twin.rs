verus!{
pub trait Tr { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl Q for A { }
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
pub trait Q { }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
impl Tr for B { }
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
} // verus!
