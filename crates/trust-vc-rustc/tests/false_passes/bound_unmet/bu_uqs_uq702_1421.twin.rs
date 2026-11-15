verus!{
impl Q for B { }
pub trait Tr { }
impl U for B {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl Tr for B { }
pub trait Q: Tr { }
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub struct Z { pub z: u8 }
impl Tr for A { }
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
} // verus!
