verus!{
impl Tr for A { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub mod m1 {
use crate::*;
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
}
impl Q for A { }
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr { self.z0() }
}
pub struct A { pub a: u8 }
impl Q for Z { }
pub struct B { pub b: u8 }
pub trait Tr { }
} // verus!
