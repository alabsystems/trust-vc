verus!{
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq0(&self) where Self: Tr + Q requires self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr + Q { self.z1() }
}
pub struct B { pub b: u8 }
impl U for A {
    proof fn rq0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub mod m2 {
use crate::*;
impl Q for A { }
}
impl U for B {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn rq0(&self) { }
}
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait Tr { }
} // verus!
