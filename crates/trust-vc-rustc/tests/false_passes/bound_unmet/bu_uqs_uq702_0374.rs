verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
impl Q for B { }
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl Tr for B { }
}
pub struct A { pub a: u8 }
pub trait Tr { }
pub trait Q: Tr { }
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
} // verus!
