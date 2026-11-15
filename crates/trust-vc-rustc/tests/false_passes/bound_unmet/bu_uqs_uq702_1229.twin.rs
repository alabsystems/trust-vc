verus!{
pub fn fA() { let _r = (A { a: 0 }).z1(); }
pub trait Tr { } impl Q for Z { }
impl Tr for Z { }
pub mod m2 {
use crate::*;
impl Tr for A { }
}
pub struct Z { pub z: u8 }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Q for A { }
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
pub struct A { pub a: u8 }
pub trait Q { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
} // verus!
