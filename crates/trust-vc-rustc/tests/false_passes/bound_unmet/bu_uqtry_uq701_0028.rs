verus!{
pub struct A { pub a: u8 }
impl Q for A { }
pub mod m1 {
use crate::*;
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
}
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub trait Q: Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl U for B {
    proof fn lm0(&self) { }
}
impl U for A {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Tr { }
impl Tr for A { }
} // verus!
