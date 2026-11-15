verus!{
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl U for B {
    proof fn rq0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
}
impl Tr for B { }
pub trait Tr { }
pub struct A { pub a: u8 }
impl Q for A { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub mod m1 {
use crate::*;
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn rq0(&self) { }
}
}
pub trait Q { }
pub struct B { pub b: u8 }
} // verus!
