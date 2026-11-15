verus!{
pub trait Tr { } impl Tr for Z { } impl Q for Z { }
pub trait Q: Tr { }
pub trait U {
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
pub mod m1 {
use crate::*;
impl Tr for A { }
}
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
} // verus!
