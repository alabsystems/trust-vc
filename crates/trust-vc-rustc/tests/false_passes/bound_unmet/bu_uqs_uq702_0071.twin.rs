verus!{
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl Q for Z { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl U for B {
    proof fn lm0(&self) { }
}
pub trait Q { }
pub mod m1 {
use crate::*;
impl Q for A { }
}
pub struct B { pub b: u8 }
pub trait Tr { }
impl U for A {
    proof fn lm0(&self) { }
}
impl Q for B { }
} // verus!
