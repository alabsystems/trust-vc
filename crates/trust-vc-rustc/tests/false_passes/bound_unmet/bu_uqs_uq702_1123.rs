verus!{
pub struct Z { pub z: u8 }
impl U for Z {
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
impl Tr for Z { }
pub trait Q { }
pub struct A { pub a: u8 }
impl Tr for A { }
pub mod m1 {
use crate::*;
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
}
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2;
}
impl Q for B { }
pub struct B { pub b: u8 }
} // verus!
