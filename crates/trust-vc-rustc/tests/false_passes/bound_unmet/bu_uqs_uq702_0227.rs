verus!{
pub fn fA() { let _r = (A { a: 0 }).z0(); }
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn rq1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn rq1(&self) where Self: Q requires self.mm() == 2;
    fn dd(&self) -> (r: u8) where Self: Q { self.z0() }
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl Tr for A { }
}
pub struct B { pub b: u8 }
pub trait Q: Tr { }
impl Q for A { }
pub trait Tr { }
impl U for Z {
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
