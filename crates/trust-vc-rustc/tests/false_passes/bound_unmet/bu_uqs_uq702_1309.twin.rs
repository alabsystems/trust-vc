verus!{
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl U for Z {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub mod m2 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
}
}
pub mod m1 {
use crate::*;
impl Tr for B { }
impl Q for A { }
}
pub struct Z { pub z: u8 }
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
impl Tr for A { }
impl Tr for Z { }
pub trait Q: Tr { }
impl Q for Z { }
pub trait Tr { }
} // verus!
