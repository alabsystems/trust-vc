verus!{
impl Tr for B { }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Tr for Z { }
impl Q for Z { }
pub mod m2 {
use crate::*;
impl Q for A { }
}
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl U for B {
    proof fn lm0(&self) { }
}
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub trait Q { }
} // verus!
