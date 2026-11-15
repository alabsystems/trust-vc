verus!{
pub struct Z { pub z: u8 }
impl Q for Z { }
pub struct A { pub a: u8 }
pub trait Q: Tr { }
impl Tr for A { }
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr + Q { self.lm1(); }
}
pub mod m2 {
use crate::*;
impl Tr for B { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for B { }
}
pub mod m1 {
use crate::*;
impl Tr for Z { }
}
pub trait Tr { }
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub struct B { pub b: u8 }
} // verus!
