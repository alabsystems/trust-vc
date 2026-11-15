verus!{
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn dd(&self) where Self: Tr + Q { self.lm0(); }
}
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
}
}
pub trait Tr { }
pub mod m1 {
use crate::*;
impl Tr for B { }
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub struct A { pub a: u8 }
impl Q for B { }
} // verus!
