verus!{
impl U<B> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U<Z> for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
}
impl Q for Z { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub trait Q: Tr { }
pub trait Tr { }
} // verus!
