verus!{
pub mod m1 {
use crate::*;
impl Q for B { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub mod m2 {
use crate::*;
impl Tr for B { }
}
impl Tr for A { }
pub trait Q: Tr { } impl Q for A { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
pub trait Tr { }
impl U for A {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
} // verus!
