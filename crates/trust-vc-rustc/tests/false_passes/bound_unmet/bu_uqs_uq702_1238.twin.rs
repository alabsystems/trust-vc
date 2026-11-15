verus!{
impl Tr for Z { }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub mod m1 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dd(&self) where Self: Tr { self.lm1(); }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl Q for A { }
}
pub struct A { pub a: u8 }
impl Q for B { }
pub trait Q { }
pub struct Z { pub z: u8 }
} // verus!
