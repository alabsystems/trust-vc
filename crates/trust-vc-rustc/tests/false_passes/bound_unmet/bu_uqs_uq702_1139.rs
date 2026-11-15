verus!{
pub mod m1 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for A { }
}
impl Q for B { }
pub mod m2 {
use crate::*;
impl Tr for A { }
}
impl Tr for B { }
pub struct B { pub b: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr + Q { self.lm1(); }
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Q { }
pub struct A { pub a: u8 }
} // verus!
