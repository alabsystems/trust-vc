verus!{
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl Q for A { }
impl Tr for A { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dd(&self) where Self: Tr { self.lm0(); }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub mod m1 {
use crate::*;
impl Tr for B { }
}
impl U for A {
    proof fn lm0(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
}
impl Q for B { }
pub trait Tr { }
pub struct A { pub a: u8 }
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
} // verus!
