verus!{
pub struct B { pub b: u8 }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn rq0(&self) { }
}
pub mod m1 {
use crate::*;
impl U for A {
    proof fn rq0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
}
impl Q for A { }
pub trait Tr { }
pub struct A { pub a: u8 }
pub trait Q { }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr { self.z1() }
}
} // verus!
