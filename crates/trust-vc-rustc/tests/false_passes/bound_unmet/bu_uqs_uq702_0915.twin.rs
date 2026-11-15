verus!{
impl Tr for B { }
pub trait Tr { }
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl Tr for A { }
}
pub trait Q: Tr { }
pub struct A { pub a: u8 }
} // verus!
