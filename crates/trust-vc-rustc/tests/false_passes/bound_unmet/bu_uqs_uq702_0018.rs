verus!{
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Q { }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl Q for B { }
pub mod m2 {
use crate::*;
impl Q for A { }
}
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
impl Tr for A { }
pub struct B { pub b: u8 }
impl Tr for Z { }
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
}
pub trait Tr { }
} // verus!
