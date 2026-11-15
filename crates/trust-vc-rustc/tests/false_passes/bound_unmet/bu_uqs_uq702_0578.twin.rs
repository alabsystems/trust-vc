verus!{
pub mod m1 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
}
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for B { }
pub trait Q: Tr { }
pub trait Tr { }
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl Tr for B { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
}
} // verus!
