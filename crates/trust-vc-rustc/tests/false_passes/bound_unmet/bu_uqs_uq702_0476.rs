verus!{
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub mod m1 {
use crate::*;
impl Q for B { }
impl Tr for A { }
}
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
impl Q for A { }
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
pub trait Q: Tr { }
impl U for Z {
    proof fn lm0(&self) { }
}
impl Tr for B { }
pub trait Tr { }
pub struct A { pub a: u8 }
} // verus!
