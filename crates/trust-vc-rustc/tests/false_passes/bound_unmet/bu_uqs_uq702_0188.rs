verus!{
pub mod m1 {
use crate::*;
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub mod m2 {
use crate::*;
impl Q for A { }
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q: Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Tr for Z { }
pub fn fA() { let _r = (A { a: 0 }).z0(); }
impl Tr for A { }
} // verus!
