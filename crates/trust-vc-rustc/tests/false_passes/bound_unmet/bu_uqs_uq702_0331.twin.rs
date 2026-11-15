verus!{
impl U for A {
    proof fn lm0(&self) { }
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl U for Z {
    proof fn lm0(&self) { }
}
impl Q for Z { }
impl Q for A { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl Tr for B { }
impl Tr for Z { }
pub trait Q { }
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl Q for B { }
}
pub trait Tr { }
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
} // verus!
