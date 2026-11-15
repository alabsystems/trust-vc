verus!{
pub struct Z { pub z: u8 }
pub trait Tr { }
impl Tr for B { }
pub trait Q { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn dd(&self) -> (r: u8) where T: Q { self.z0() }
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
}
impl U<B> for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl U<B> for A {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
}
impl U<Z> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for Z { }
pub struct B { pub b: u8 }
} // verus!
