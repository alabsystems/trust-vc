verus!{
pub trait Tr { }
pub trait Q { }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub fn fZ() { let _r = (Z { z: 0 }).z1(); }
pub mod m1 {
use crate::*;
impl U for B {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
}
impl Q for B { }
impl Tr for B { }
impl Tr for Z { }
impl Q for A { }
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr { self.z0() }
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
} // verus!
