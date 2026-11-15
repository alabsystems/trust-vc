verus!{
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait Q: Tr { }
pub trait U {
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
}
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
}
}
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl Tr for A { }
}
} // verus!
