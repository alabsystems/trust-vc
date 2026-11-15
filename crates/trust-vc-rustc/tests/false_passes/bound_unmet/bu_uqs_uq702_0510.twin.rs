verus!{
impl U for Z {
    proof fn lm0(&self) { }
}
impl U for A {
    proof fn lm0(&self) { }
}
impl Q for A { }
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl Tr for A { }
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub trait Q { }
pub trait Tr { }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
} // verus!
