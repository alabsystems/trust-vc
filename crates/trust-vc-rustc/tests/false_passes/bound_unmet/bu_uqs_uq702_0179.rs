verus!{
impl U for A {
    proof fn lm0(&self) { }
}
pub mod m2 {
use crate::*;
impl Tr for B { }
}
pub trait Q: Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl Q for A { }
pub struct B { pub b: u8 }
impl U for Z {
    proof fn lm0(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
}
pub trait Tr { }
impl Tr for A { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
} // verus!
