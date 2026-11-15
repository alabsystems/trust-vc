verus!{
pub struct Z { pub z: u8 }
impl U for B {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
pub struct A { pub a: u8 }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Q for A { }
pub trait Tr { }
pub trait Q { }
impl Tr for B { }
pub mod m2 {
use crate::*;
impl Q for B { }
}
} // verus!
