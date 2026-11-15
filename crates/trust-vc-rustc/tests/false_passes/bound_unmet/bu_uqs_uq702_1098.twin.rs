verus!{
pub struct B { pub b: u8 } impl Tr for Z { } impl Q for Z { }
pub trait Q { }
pub struct A { pub a: u8 }
pub mod m2 {
use crate::*;
impl Tr for B { }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
pub proof fn fA() { (A { a: 0 }).lm0(); }
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl Q for A { }
impl Tr for A { }
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
impl U for B {
    proof fn lm0(&self) { }
}
} // verus!
