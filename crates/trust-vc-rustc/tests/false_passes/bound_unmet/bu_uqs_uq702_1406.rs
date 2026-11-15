verus!{
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
pub mod m2 {
use crate::*;
impl Q for B { }
impl U for Z {
    proof fn lm0(&self) { }
}
}
pub trait Q: Tr { }
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl Tr for Z { }
impl U for B {
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl Tr for B { }
pub trait Tr { }
impl Q for Z { }
} // verus!
