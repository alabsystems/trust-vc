verus!{
impl Q for A { }
pub trait Q: Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl Tr for A { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub mod m1 {
use crate::*;
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait Tr { }
} // verus!
