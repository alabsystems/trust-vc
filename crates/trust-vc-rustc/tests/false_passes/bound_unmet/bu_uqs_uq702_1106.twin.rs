verus!{
pub struct A { pub a: u8 }
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl Tr for Z { }
impl Tr for B { }
impl Q for B { }
}
pub trait Q: Tr { }
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
}
impl Tr for A { }
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl Q for A { }
pub mod m2 {
use crate::*;
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
} // verus!
