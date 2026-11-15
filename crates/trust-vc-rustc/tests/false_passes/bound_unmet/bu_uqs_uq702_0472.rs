verus!{
pub struct Z { pub z: u8 }
impl Tr for Z { }
impl U for B {
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub struct A { pub a: u8 }
pub trait Q: Tr { }
impl Tr for A { }
pub mod m1 {
use crate::*;
impl Tr for B { }
}
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
impl Q for B { }
impl U for A {
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm0(&self) { }
}
pub mod m2 {
use crate::*;
impl Q for A { }
}
} // verus!
