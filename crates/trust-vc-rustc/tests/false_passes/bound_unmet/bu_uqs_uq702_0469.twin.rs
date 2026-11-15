verus!{
impl Q for Z { }
pub trait Tr { }
pub mod m2 {
use crate::*;
impl Tr for Z { }
impl Tr for A { }
}
impl U for B {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl Tr for B { }
}
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
pub struct A { pub a: u8 }
} // verus!
