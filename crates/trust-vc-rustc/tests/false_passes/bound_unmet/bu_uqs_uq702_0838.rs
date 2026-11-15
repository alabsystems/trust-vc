verus!{
impl U for B {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub trait Q { }
pub mod m2 {
use crate::*;
impl Q for Z { }
}
impl Tr for Z { }
impl U for A {
    proof fn lm0(&self) { }
}
impl Q for B { }
pub struct A { pub a: u8 }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
impl Tr for A { }
impl Q for A { }
impl U for Z {
    proof fn lm0(&self) { }
}
} // verus!
