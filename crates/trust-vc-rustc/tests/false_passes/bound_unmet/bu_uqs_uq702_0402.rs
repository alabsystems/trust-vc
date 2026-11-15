verus!{
impl Tr for B { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub trait Tr { }
impl U for A {
    proof fn lm0(&self) { }
}
impl Tr for Z { }
pub mod m1 {
use crate::*;
impl Tr for A { }
}
pub trait Q: Tr { }
impl U for B {
    proof fn lm0(&self) { }
}
impl Q for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub mod m2 {
use crate::*;
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
}
} // verus!
