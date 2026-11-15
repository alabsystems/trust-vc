verus!{
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
pub trait Tr { }
impl Q for Z { }
pub struct Z { pub z: u8 }
impl Tr for A { }
pub struct A { pub a: u8 }
pub trait Q { }
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
} // verus!
