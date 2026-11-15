verus!{
pub struct A { pub a: u8 }
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
pub mod m1 {
use crate::*;
impl Tr for A { }
}
impl U for Z {
    proof fn lm0(&self) { }
}
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn dd(&self) where Self: Q { self.lm0(); }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl Tr for B { }
pub struct B { pub b: u8 }
impl Q for A { }
pub trait Tr { }
pub trait Q { }
pub struct Z { pub z: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
} // verus!
