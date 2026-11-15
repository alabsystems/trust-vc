verus!{
impl Q for A { }
pub mod m1 {
use crate::*;
impl Tr for B { }
}
pub struct A { pub a: u8 }
pub mod m2 {
use crate::*;
impl Tr for Z { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
pub trait Q { }
impl Tr for A { }
impl Q for B { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
} // verus!
