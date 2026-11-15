verus!{
pub struct A { pub a: u8 }
pub trait Q: Tr { }
impl U for A {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl Tr for A { }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
impl Q for A { }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl Q for Z { }
}
impl U for Z {
    proof fn lm0(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
}
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
} // verus!
