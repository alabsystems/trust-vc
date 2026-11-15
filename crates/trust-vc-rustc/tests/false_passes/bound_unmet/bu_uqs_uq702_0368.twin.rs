verus!{
pub mod m1 {
use crate::*;
impl Q for B { }
}
impl Q for A { }
impl U for A {
    proof fn lm0(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
} // verus!
