verus!{
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub fn fB() { let _r = (B { b: 0 }).z0(); }
pub mod m1 {
use crate::*;
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
}
pub struct Z { pub z: u8 }
impl Tr for B { }
pub struct B { pub b: u8 }
pub trait Q { }
impl Tr for Z { }
impl Q for B { }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr + Q { self.z0() }
}
pub struct A { pub a: u8 }
} // verus!
