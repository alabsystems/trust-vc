verus!{
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
}
}
impl Q for B { }
pub trait Tr { }
pub trait Q { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub proof fn fA() { (A { a: 0 }).lm0(); }
impl U for A {
    proof fn lm0(&self) { }
}
impl Tr for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn dd(&self) where Self: Q { self.lm0(); }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl Q for A { }
} // verus!
