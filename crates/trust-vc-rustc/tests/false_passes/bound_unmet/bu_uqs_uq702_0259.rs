verus!{
impl Tr for A { }
pub trait Q: Tr { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl Tr for B { }
pub mod m2 {
use crate::*;
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Q for B { }
}
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
} // verus!
