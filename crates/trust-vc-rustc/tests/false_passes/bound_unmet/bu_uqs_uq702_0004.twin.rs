verus!{
impl Q for B { }
impl Tr for B { }
impl Tr for A { }
pub trait Q: Tr { }
pub trait Tr { }
pub struct B { pub b: u8 }
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
impl Tr for Z { }
} // verus!
