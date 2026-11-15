verus!{
impl U for A {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub trait Q { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
pub trait Tr { }
pub mod m2 {
use crate::*;
impl Tr for B { }
impl Tr for A { }
}
impl U for B {
    proof fn lm0(&self) { }
}
impl Q for B { }
} // verus!
