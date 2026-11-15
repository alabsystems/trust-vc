verus!{
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait Q: Tr { }
pub mod m2 {
use crate::*;
impl U<A> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
    fn dd(&self) -> (r: u8) where T: Tr + Q { self.z0() }
}
impl U<A> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
} // verus!
