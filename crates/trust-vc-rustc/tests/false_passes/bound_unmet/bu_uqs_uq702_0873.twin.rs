verus!{
impl Tr for B { }
pub struct B { pub b: u8 } impl Q for A { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
impl Tr for Z { }
impl Tr for A { }
impl Q for B { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub trait Q: Tr { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
pub mod m1 {
use crate::*;
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
}
}
} // verus!
