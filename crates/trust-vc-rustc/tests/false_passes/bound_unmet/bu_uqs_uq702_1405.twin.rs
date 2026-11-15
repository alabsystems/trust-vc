verus!{
pub trait Tr { }
impl U for A {
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
}
impl Q for Z { }
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
pub struct B { pub b: u8 }
impl Q for A { }
impl U for B {
    proof fn lm0(&self) { }
}
impl Tr for A { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
} // verus!
