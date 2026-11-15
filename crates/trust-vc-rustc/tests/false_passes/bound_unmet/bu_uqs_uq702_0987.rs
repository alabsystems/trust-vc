verus!{
pub struct B { pub b: u8 }
pub fn fA() { let _r = (A { a: 0 }).z0(); }
pub trait Q { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
impl U for A {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub mod m2 {
use crate::*;
impl Q for A { }
}
impl Tr for A { }
pub trait Tr { }
pub struct Z { pub z: u8 }
} // verus!
