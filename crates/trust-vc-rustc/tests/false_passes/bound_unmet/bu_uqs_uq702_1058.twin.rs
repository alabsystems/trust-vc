verus!{
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub struct B { pub b: u8 } impl Tr for Z { } impl Q for Z { }
pub proof fn fA() { (A { a: 0 }).lm0(); }
impl U for B {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
impl Q for A { }
impl Tr for A { }
pub trait Q: Tr { }
impl Tr for B { }
impl Q for B { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
}
} // verus!
