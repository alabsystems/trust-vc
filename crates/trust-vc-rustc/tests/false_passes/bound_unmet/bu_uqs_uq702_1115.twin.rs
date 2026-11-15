verus!{
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl Q for A { }
}
pub trait Tr { }
impl Tr for A { }
pub trait Q: Tr { }
} // verus!
