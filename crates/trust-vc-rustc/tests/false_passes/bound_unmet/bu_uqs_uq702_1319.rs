verus!{
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub mod m2 {
use crate::*;
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait Tr { }
pub trait Q { }
pub struct B { pub b: u8 }
impl Q for Z { }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
pub struct A { pub a: u8 }
} // verus!
