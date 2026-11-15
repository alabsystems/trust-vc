verus!{
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub trait Tr { } impl Tr for A { }
pub struct A { pub a: u8 }
impl Q for A { }
pub trait Q { }
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl Q for Z { }
impl Tr for Z { }
pub struct Z { pub z: u8 }
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
pub struct B { pub b: u8 }
} // verus!
