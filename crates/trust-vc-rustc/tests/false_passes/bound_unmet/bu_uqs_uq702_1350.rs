verus!{
pub trait Q { }
pub struct B { pub b: u8 }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl Tr for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub mod m1 {
use crate::*;
impl Q for A { }
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Q for B { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
impl Tr for Z { }
} // verus!
