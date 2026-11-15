verus!{
pub struct B { pub b: u8 } impl Q for A { }
pub trait Tr { }
impl Q for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl Q for B { }
}
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
pub struct A { pub a: u8 }
impl U for Z {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
impl Tr for B { }
pub trait Q { }
impl Tr for A { }
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl U for A {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
} // verus!
