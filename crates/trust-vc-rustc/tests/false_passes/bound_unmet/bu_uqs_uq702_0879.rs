verus!{
impl U for A {
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub mod m1 {
use crate::*;
impl Q for B { }
}
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub trait Q { }
impl Tr for B { }
impl Q for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2;
}
pub trait Tr { }
impl U for B {
    proof fn rq1(&self) { assert(self.mm() == 2); }
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
