verus!{
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Tr { }
impl U for A {
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm0(&self) { }
}
impl Tr for B { }
pub trait Q { }
impl Q for A { }
pub mod m2 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
}
pub struct A { pub a: u8 }
impl Tr for Z { }
} // verus!
