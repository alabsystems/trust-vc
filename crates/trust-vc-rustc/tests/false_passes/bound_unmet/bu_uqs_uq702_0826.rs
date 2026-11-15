verus!{
impl U for B {
    proof fn lm0(&self) { }
}
pub trait Q { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub trait Tr { }
impl Q for A { }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
pub struct A { pub a: u8 }
} // verus!
