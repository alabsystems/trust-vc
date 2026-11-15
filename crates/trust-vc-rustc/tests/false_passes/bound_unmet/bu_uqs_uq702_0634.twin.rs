verus!{
impl U<A> for Z {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for A { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub mod m1 {
use crate::*;
impl Q for B { }
}
impl U<B> for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    fn z1(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where T: Tr { self.z0() }
}
pub mod m2 {
use crate::*;
impl Q for A { }
}
pub struct A { pub a: u8 }
pub trait Q { }
} // verus!
