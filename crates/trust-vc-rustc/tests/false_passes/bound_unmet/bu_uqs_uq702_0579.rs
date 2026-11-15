verus!{
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait U {
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub struct A { pub a: u8 }
pub trait Q: Tr { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for Z { }
pub mod m1 {
use crate::*;
impl Tr for Z { }
}
pub trait Tr { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
} // verus!
