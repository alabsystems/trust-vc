verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub trait Q { }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub mod m2 {
use crate::*;
impl Tr for A { }
}
} // verus!
