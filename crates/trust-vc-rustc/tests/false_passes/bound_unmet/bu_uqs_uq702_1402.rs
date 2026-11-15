verus!{
impl U for Z {
    proof fn lm0(&self) { }
}
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl Tr for A { }
pub trait Tr { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl Tr for Z { }
pub mod m2 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
}
}
pub struct Z { pub z: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
pub trait Q { }
impl Q for B { }
impl Q for A { }
} // verus!
