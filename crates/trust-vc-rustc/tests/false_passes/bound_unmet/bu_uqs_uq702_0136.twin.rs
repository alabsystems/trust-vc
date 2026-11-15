verus!{
pub mod m2 {
use crate::*;
impl Q for A { }
}
pub trait Tr { }
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
pub proof fn fA() { (A { a: 0 }).lm0(); }
pub struct Z { pub z: u8 }
pub mod m1 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
}
impl Tr for A { }
impl Tr for B { }
}
pub struct B { pub b: u8 }
impl U for Z {
    proof fn lm0(&self) { }
}
impl Q for Z { }
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
} // verus!
