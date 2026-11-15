verus!{
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
impl Q for B { }
pub trait Tr { }
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
}
impl Q for A { }
pub fn fA() { let _r = (A { a: 0 }).z0(); }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
pub struct Z { pub z: u8 }
} // verus!
