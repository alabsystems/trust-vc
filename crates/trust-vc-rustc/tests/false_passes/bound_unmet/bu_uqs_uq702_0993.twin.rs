verus!{
pub struct B { pub b: u8 }
pub trait Q { }
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl Q for B { }
impl Tr for B { }
pub mod m2 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
}
}
pub trait Tr { }
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dd(&self) where Self: Tr + Q { self.lm0(); }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl Tr for A { }
impl Q for A { }
} // verus!
