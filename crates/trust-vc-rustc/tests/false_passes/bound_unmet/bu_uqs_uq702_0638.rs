verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for B { }
pub trait Q { }
pub struct Z { pub z: u8 }
impl Tr for A { }
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl Q for A { }
}
pub trait Tr { }
pub struct A { pub a: u8 }
pub mod m2 {
use crate::*;
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
}
} // verus!
