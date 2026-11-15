verus!{
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl Q for A { }
pub trait Q { }
pub mod m1 {
use crate::*;
impl Tr for A { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
impl U for A {
    proof fn lm0(&self) { }
}
pub trait Tr { }
impl Q for B { }
impl U for B {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
} // verus!
