verus!{
pub fn fB() { let _r = (B { b: 0 }).z0(); }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub mod m2 {
use crate::*;
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn dd(&self) -> (r: u8) where Self: Tr + Q { self.z0() }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
impl Tr for B { }
impl Q for A { }
pub struct B { pub b: u8 }
pub trait Q: Tr { }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
impl Q for B { }
impl Tr for A { }
pub struct A { pub a: u8 }
} // verus!
