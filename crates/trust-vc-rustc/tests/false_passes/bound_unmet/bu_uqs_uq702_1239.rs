verus!{
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
impl U for B {
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl Tr for A { }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl Q for A { }
impl Tr for B { }
}
pub struct B { pub b: u8 }
impl Q for B { }
pub struct A { pub a: u8 }
pub trait Q { }
} // verus!
