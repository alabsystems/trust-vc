verus!{
pub struct Z { pub z: u8 } impl Tr for Z { } impl Q for Z { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl Tr for A { }
impl Q for A { }
}
pub proof fn fA() { (A { a: 0 }).lm0(); }
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub trait Q { }
impl U for A {
    proof fn lm0(&self) { }
}
} // verus!
