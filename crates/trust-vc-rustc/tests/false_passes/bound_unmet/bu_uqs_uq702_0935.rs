verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub trait Q: Tr { }
impl U for B {
    proof fn lm0(&self) { }
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl U for A {
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl Q for B { }
impl Tr for B { }
}
impl Tr for A { }
} // verus!
