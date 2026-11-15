verus!{
impl Tr for B { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Q { }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl Tr for A { }
}
pub mod m1 {
use crate::*;
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
}
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Q for B { }
} // verus!
