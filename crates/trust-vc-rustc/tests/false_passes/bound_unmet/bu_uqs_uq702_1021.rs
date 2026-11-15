verus!{
impl Tr for A { }
pub trait Q { }
pub trait Tr { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
}
pub mod m2 {
use crate::*;
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub struct B { pub b: u8 }
impl Q for A { }
} // verus!
