verus!{
pub trait Tr { }
impl Tr for A { }
impl U for B {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait Q: Tr { }
pub struct B { pub b: u8 }
impl Tr for B { }
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
} // verus!
