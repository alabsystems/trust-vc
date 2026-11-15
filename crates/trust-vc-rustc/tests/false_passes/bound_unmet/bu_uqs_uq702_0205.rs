verus!{
pub mod m1 {
use crate::*;
impl Tr for B { }
}
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
pub struct Z { pub z: u8 }
pub proof fn fA() { (A { a: 0 }).lm0(); }
pub struct B { pub b: u8 }
impl Tr for A { }
pub trait U {
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub trait Tr { }
impl U for B {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl Q for A { }
pub trait Q { }
} // verus!
