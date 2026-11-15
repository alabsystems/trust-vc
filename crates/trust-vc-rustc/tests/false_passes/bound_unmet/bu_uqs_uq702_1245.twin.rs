verus!{
pub proof fn fA() { (A { a: 0 }).lm0(); }
impl U for A {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub trait Q { }
impl Q for A { }
impl Q for B { }
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl Tr for B { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl Tr for A { }
impl U for B {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
}
}
} // verus!
