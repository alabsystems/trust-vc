verus!{
impl Q for B { }
impl Tr for A { }
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
}
}
impl Q for A { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub trait Q { }
impl Tr for B { }
pub trait Tr { }
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
} // verus!
