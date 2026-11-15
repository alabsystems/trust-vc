verus!{
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { } impl Tr for A { }
pub mod m1 {
use crate::*;
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
}
pub struct A { pub a: u8 }
impl Q for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl Tr for B { }
pub trait Q { }
impl Q for B { }
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub struct B { pub b: u8 }
} // verus!
