verus!{
pub trait Q: Tr { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr { self.z0() }
}
pub struct Z { pub z: u8 }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub mod m2 {
use crate::*;
impl Q for A { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
}
impl Tr for A { }
pub trait Tr { }
} // verus!
