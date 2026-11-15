verus!{
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q { }
impl Q for B { }
impl U for B {
    proof fn lm0(&self) { }
}
impl U for A {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl Tr for A { }
}
impl Q for A { }
pub struct A { pub a: u8 }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl U for Z {
    proof fn lm0(&self) { }
}
} // verus!
