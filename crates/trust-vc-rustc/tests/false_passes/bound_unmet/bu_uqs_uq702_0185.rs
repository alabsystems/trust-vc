verus!{
impl Tr for B { }
pub struct Z { pub z: u8 }
impl Q for A { }
pub mod m2 {
use crate::*;
impl Tr for A { }
impl U for A {
    proof fn lm0(&self) { }
}
}
pub trait Q { }
impl U for B {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait Tr { }
} // verus!
