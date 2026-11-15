verus!{
pub mod m1 {
use crate::*;
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn dd(&self) -> (r: u8) where Self: Q { self.z0() }
}
impl Q for A { }
impl Tr for B { }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for A { }
pub fn fA() { let _r = (A { a: 0 }).z0(); }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub trait Q: Tr { }
pub trait Tr { }
pub struct A { pub a: u8 }
} // verus!
