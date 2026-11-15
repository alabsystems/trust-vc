verus!{
impl Tr for A { }
impl U for A {
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
}
}
pub struct A { pub a: u8 }
impl Tr for B { }
pub struct Z { pub z: u8 }
impl Q for A { }
pub proof fn fA() { (A { a: 0 }).lm0(); }
impl U for Z {
    proof fn lm0(&self) { }
}
impl Q for B { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub trait Tr { }
pub struct B { pub b: u8 }
pub trait Q { }
} // verus!
