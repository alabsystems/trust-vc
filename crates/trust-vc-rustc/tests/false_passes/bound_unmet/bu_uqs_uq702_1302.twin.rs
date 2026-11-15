verus!{
pub struct A { pub a: u8 }
pub trait Tr { }
pub struct B { pub b: u8 }
pub trait Q { }
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
}
pub mod m2 {
use crate::*;
impl Tr for B { }
}
pub struct Z { pub z: u8 }
} // verus!
