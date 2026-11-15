verus!{
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub fn fA() { let _r = (A { a: 0 }).z0(); }
pub trait Tr { }
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
impl Q for Z { }
impl Q for A { }
impl Tr for A { }
pub mod m2 {
use crate::*;
impl Q for B { }
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
} // verus!
