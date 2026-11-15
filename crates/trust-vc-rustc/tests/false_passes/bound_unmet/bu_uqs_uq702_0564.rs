verus!{
impl Q for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
impl Q for B { }
impl U for B {
    proof fn lm0(&self) { }
}
pub trait Q { }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl Tr for A { }
}
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
} // verus!
