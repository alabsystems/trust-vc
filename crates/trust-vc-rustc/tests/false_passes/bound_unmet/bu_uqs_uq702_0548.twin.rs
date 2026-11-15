verus!{
pub struct A { pub a: u8 }
pub trait Tr { }
impl Tr for B { }
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl Q for B { }
}
impl Q for A { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait U {
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dd(&self) where Self: Tr + Q { self.lm0(); }
}
impl U for A {
    proof fn lm0(&self) { }
}
pub trait Q { }
} // verus!
