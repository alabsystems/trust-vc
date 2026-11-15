verus!{
pub mod m1 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
}
}
impl Q for B { }
pub trait Q { }
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
pub trait U {
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn dd(&self) where Self: Tr + Q { self.lm0(); }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl Tr for B { }
} // verus!
