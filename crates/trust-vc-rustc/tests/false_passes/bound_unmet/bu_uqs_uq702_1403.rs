verus!{
impl Tr for A { }
pub struct Z { pub z: u8 }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
pub mod m2 {
use crate::*;
impl Q for B { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub fn fA() { let _r = (A { a: 0 }).z0(); }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl Q for A { }
} // verus!
