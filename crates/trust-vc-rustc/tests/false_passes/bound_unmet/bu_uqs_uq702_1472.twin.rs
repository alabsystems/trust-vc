verus!{
pub trait Q { }
impl Q for A { }
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Q for B { }
}
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
impl Tr for Z { }
} // verus!
