verus!{
impl Q for A { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait Q: Tr { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl Tr for A { }
pub mod m1 {
use crate::*;
impl Tr for Z { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
}
pub mod m2 {
use crate::*;
impl Tr for B { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr + Q { self.lm0(); }
}
impl Q for B { }
} // verus!
