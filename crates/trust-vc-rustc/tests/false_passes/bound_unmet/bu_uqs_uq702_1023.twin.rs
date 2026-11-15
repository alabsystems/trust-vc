verus!{
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
pub trait Q { }
impl Tr for A { }
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
impl Q for Z { }
pub mod m1 {
use crate::*;
impl Q for B { }
}
pub mod m2 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
}
}
impl Tr for Z { }
pub trait Tr { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl U for Z {
    proof fn lm0(&self) { }
}
pub proof fn fA() { (A { a: 0 }).lm0(); }
} // verus!
