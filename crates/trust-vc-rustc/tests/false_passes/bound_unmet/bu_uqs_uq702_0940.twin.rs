verus!{
impl Tr for A { }
pub struct A { pub a: u8 } impl Q for A { }
impl Q for B { }
pub struct Z { pub z: u8 }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub trait Q: Tr { }
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn dd(&self) -> (r: u8) where Self: Q { self.z0() }
}
pub struct B { pub b: u8 }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
pub mod m2 {
use crate::*;
impl Tr for B { }
}
} // verus!
