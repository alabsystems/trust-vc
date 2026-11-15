verus!{
pub struct Z { pub z: u8 } impl Tr for Z { }
pub mod m2 {
use crate::*;
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
}
impl Tr for A { }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Q for Z { }
pub struct A { pub a: u8 }
impl Q for A { }
pub trait Q { }
pub struct B { pub b: u8 }
} // verus!
