verus!{
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub trait Q: Tr { }
pub mod m2 {
use crate::*;
impl Tr for A { }
}
impl Q for A { }
pub struct A { pub a: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl Tr for B { }
}
pub struct Z { pub z: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
} // verus!
