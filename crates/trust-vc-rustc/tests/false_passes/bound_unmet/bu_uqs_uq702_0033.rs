verus!{
impl Q for Z { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
pub trait Q { }
impl U for B {
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2;
}
impl Q for B { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
impl Tr for A { }
}
impl Q for A { }
} // verus!
