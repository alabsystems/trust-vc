verus!{
impl Tr for A { }
pub struct A { pub a: u8 }
impl Q for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub trait Tr { }
pub struct B { pub b: u8 }
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
impl Tr for Z { }
}
pub trait Q: Tr { }
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
} // verus!
