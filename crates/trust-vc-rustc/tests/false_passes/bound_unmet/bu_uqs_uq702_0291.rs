verus!{
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
impl U<B> for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
impl Tr for B { }
pub struct A { pub a: u8 }
impl Q for Z { }
pub trait Tr { }
pub mod m2 {
use crate::*;
impl U<Z> for Z {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
}
impl Q for B { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
    fn dd(&self) -> (r: u8) where T: Tr + Q { self.z0() }
}
} // verus!
