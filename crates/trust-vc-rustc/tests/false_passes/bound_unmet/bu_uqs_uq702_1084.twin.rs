verus!{
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
impl Q for B { }
impl Tr for Z { }
impl Tr for A { }
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn dd(&self) -> (r: u8) where Self: Tr + Q { self.z0() }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
pub struct B { pub b: u8 }
impl Q for A { }
pub mod m1 {
use crate::*;
impl U for B {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Q { }
} // verus!
