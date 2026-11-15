verus!{
pub struct A { pub a: u8 } impl Q for A { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait U {
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
}
impl Tr for A { }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
pub trait Tr { }
} // verus!
