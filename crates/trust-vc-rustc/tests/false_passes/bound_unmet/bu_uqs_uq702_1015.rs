verus!{
pub struct B { pub b: u8 }
pub trait Q: Tr { }
pub trait Tr { }
pub struct A { pub a: u8 }
pub fn fB() { let _r = (B { b: 0 }).z0(); }
impl Tr for A { }
pub struct Z { pub z: u8 }
pub mod m1 {
use crate::*;
impl U for B {
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2;
}
pub mod m2 {
use crate::*;
impl Tr for B { }
}
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
} // verus!
