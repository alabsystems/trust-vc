verus!{
impl Q for A { }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl Tr for A { }
}
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait Q: Tr { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl Tr for B { }
impl U for A {
    proof fn lm0(&self) { }
}
} // verus!
