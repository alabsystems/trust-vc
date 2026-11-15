verus!{
pub struct B { pub b: u8 }
pub trait Q { }
pub proof fn fZ() { (Z { z: 0 }).lm0(); }
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
impl Q for B { }
impl U for Z {
    proof fn lm0(&self) { }
}
impl Q for Z { }
pub trait Tr { }
impl Tr for A { }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub struct A { pub a: u8 }
} // verus!
