verus!{
pub trait Tr { }
impl U for A {
    proof fn lm0(&self) { }
}
impl Q for B { }
pub trait Q { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
impl Tr for B { }
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
}
}
impl Tr for A { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
} // verus!
