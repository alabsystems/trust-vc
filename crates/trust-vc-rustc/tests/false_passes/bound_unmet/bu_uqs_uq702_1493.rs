verus!{
impl Tr for A { }
pub mod m2 {
use crate::*;
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
pub struct B { pub b: u8 }
impl Tr for Z { }
pub trait Q: Tr { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
impl Tr for B { }
pub struct Z { pub z: u8 }
impl Q for A { }
pub struct A { pub a: u8 }
} // verus!
