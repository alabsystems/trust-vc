verus!{
pub mod m2 {
use crate::*;
impl Tr for A { }
}
pub struct Z { pub z: u8 }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl Q for A { }
impl Tr for B { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
pub trait Tr { }
pub trait Q { }
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for B { }
pub proof fn fA() { (A { a: 0 }).lm0(); }
} // verus!
