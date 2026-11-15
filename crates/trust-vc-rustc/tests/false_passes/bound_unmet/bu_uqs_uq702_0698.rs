verus!{
pub trait Q { }
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl Tr for B { }
impl Tr for A { }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
impl Q for A { }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub mod m2 {
use crate::*;
impl Q for Z { }
}
pub struct B { pub b: u8 }
} // verus!
