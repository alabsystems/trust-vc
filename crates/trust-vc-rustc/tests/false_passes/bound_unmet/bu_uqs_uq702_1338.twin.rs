verus!{
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Tr for Z { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl Q for A { }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
impl U for B {
    proof fn lm0(&self) { }
}
} // verus!
