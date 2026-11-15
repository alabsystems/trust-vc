verus!{
pub struct Z { pub z: u8 }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl Q for A { }
impl Tr for A { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub mod m2 {
use crate::*;
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub struct B { pub b: u8 }
pub trait Q { }
pub struct A { pub a: u8 }
impl Tr for B { }
impl Q for Z { }
impl Q for B { }
} // verus!
