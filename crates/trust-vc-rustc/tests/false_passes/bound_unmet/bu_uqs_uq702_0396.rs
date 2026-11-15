verus!{
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
impl Tr for A { }
pub struct A { pub a: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm1(); }
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
}
impl Q for A { }
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl Tr for Z { }
impl U for A {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
}
}
} // verus!
