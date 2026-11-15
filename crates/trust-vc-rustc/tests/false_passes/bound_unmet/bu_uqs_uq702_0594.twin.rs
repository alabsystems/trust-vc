verus!{
pub mod m2 {
use crate::*;
impl Q for A { }
}
impl Tr for A { }
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Q { self.z0() }
}
pub struct B { pub b: u8 }
pub trait Tr { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
