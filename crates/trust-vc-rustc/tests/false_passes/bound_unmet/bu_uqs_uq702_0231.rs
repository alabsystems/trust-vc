verus!{
pub fn fB() { let _r = (B { b: 0 }).z0(); }
pub mod m2 {
use crate::*;
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
}
pub trait Tr { }
pub trait Q { }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub mod m1 {
use crate::*;
impl Q for B { }
}
pub struct B { pub b: u8 }
impl Tr for Z { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
impl Tr for B { }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
pub struct A { pub a: u8 }
} // verus!
