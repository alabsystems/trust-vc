verus!{
impl Q for A { }
pub mod m1 {
use crate::*;
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr { self.z0() }
}
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl Q for B { }
impl Tr for A { }
pub fn fA() { let _r = (A { a: 0 }).z0(); }
pub trait Tr { }
pub trait Q { }
} // verus!
