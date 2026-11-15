verus!{
impl Q for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
pub trait Tr { }
impl Tr for A { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub trait Q: Tr { }
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
} // verus!
