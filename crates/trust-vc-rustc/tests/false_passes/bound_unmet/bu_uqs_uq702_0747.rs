verus!{
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub mod m1 {
use crate::*;
impl Tr for A { }
impl Q for A { }
impl Q for B { }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait Q { }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for B { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
pub fn fA() { let _r = (A { a: 0 }).z0(); }
} // verus!
