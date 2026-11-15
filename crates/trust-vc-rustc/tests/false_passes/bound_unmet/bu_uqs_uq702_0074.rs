verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr + Q { self.lm0(); }
}
impl Tr for B { }
impl Q for B { }
impl U for A {
    proof fn lm0(&self) { }
}
pub trait Q: Tr { }
pub mod m1 {
use crate::*;
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
}
pub struct B { pub b: u8 }
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
} // verus!
