verus!{
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub mod m2 {
use crate::*;
impl Q for A { }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
impl Tr for B { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub trait Q { }
} // verus!
