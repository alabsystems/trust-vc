verus!{
impl Q for B { }
pub mod m1 {
use crate::*;
impl Tr for B { }
}
pub fn fB() { let _r = (B { b: 0 }).z0(); }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait Q { }
pub struct A { pub a: u8 }
impl Tr for A { }
impl U for B {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm1(); }
}
pub struct B { pub b: u8 }
} // verus!
