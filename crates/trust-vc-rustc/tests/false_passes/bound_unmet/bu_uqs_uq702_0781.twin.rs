verus!{
pub trait Tr { } impl Tr for A { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
impl Tr for Z { }
impl Q for A { }
pub mod m2 {
use crate::*;
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub struct Z { pub z: u8 }
} // verus!
