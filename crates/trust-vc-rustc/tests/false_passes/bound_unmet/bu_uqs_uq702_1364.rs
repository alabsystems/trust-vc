verus!{
pub proof fn fA() { (A { a: 0 }).lm0(); }
pub struct Z { pub z: u8 }
pub trait Q: Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl U for B {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl Tr for A { }
pub struct B { pub b: u8 }
impl Q for A { }
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
}
}
pub mod m2 {
use crate::*;
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
}
pub trait Tr { }
} // verus!
