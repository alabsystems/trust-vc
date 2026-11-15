verus!{
pub struct Z { pub z: u8 }
impl Q for B { }
pub mod m1 {
use crate::*;
impl Tr for A { }
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr { self.z0() }
}
pub trait Q { }
impl Q for Z { }
pub trait Tr { }
pub struct B { pub b: u8 }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for B { }
pub mod m2 {
use crate::*;
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub struct A { pub a: u8 }
} // verus!
