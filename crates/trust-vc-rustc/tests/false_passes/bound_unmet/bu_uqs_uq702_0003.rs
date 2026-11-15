verus!{
impl U for Z {
    proof fn lm0(&self) { }
}
impl Tr for B { }
pub trait Q { }
impl U for B {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Tr { }
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
impl U for A {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl Q for A { }
pub struct A { pub a: u8 }
impl Q for B { }
} // verus!
