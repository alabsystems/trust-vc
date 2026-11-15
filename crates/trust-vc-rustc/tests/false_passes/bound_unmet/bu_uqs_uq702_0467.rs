verus!{
pub trait Tr { }
impl Q for B { }
impl Q for Z { }
pub struct Z { pub z: u8 }
impl Tr for B { }
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn dd(&self) where Self: Tr { self.lm0(); }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub struct A { pub a: u8 }
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub trait Q { }
pub mod m2 {
use crate::*;
impl Q for A { }
impl U for Z {
    proof fn lm0(&self) { }
}
impl U for A {
    proof fn lm0(&self) { }
}
}
impl U for B {
    proof fn lm0(&self) { }
}
} // verus!
