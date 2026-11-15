verus!{
impl Q for Z { }
pub mod m1 {
use crate::*;
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
}
pub struct A { pub a: u8 }
pub trait Tr { }
impl U for A {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
impl Q for A { }
pub mod m2 {
use crate::*;
impl Q for B { }
}
pub struct Z { pub z: u8 }
pub trait Q { }
impl Tr for B { }
impl U for B {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
impl Tr for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
} // verus!
