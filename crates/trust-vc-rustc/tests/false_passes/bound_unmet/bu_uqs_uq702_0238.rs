verus!{
pub struct A { pub a: u8 }
impl Q for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
impl U for A {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct B { pub b: u8 }
} // verus!
