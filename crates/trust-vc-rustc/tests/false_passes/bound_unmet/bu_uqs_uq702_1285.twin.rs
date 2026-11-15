verus!{
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Tr for A { }
}
pub proof fn fA() { (A { a: 0 }).lm0(); }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl Q for A { }
} // verus!
