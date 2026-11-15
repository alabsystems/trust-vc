verus!{
pub trait Tr { } impl Tr for A { } impl Q for A { }
pub mod m1 {
use crate::*;
impl Tr for B { }
}
pub struct A { pub a: u8 }
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl U for B {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub trait Q: Tr { }
pub struct B { pub b: u8 }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Q for B { }
} // verus!
