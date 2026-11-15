verus!{
pub trait Tr { }
impl Tr for Z { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub struct A { pub a: u8 }
impl U for B {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub proof fn fA() { (A { a: 0 }).lm0(); }
pub mod m2 {
use crate::*;
impl Q for A { }
}
pub trait Q: Tr { }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Tr for A { }
} // verus!
