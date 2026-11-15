verus!{
pub struct A { pub a: u8 }
impl Q for A { }
impl Q for Z { }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub proof fn fA() { (A { a: 0 }).lm0(); }
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
}
}
pub trait Q { }
pub trait Tr { }
impl U for A {
    proof fn lm0(&self) { }
}
impl Tr for A { }
} // verus!
