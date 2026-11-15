verus!{
pub mod m2 {
use crate::*;
impl U for B {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait Q: Tr { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub trait Tr { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl Tr for A { }
impl Tr for B { }
impl Q for B { }
} // verus!
