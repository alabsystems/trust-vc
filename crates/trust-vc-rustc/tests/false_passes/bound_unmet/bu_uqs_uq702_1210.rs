verus!{
pub struct Z { pub z: u8 }
pub trait Tr { }
impl Tr for B { }
pub trait Q { }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
}
impl Q for B { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    proof fn rq1(&self) where Self: Tr + Q requires self.mm() == 2;
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
} // verus!
