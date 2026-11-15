verus!{
impl Tr for Z { }
impl Tr for B { }
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait U<T> {
    fn z0(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    fn z1(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
}
pub trait Q: Tr { }
impl U<A> for Z {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub mod m2 {
use crate::*;
impl Q for Z { }
}
impl Q for B { }
pub struct Z { pub z: u8 }
impl U<Z> for B {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
impl U<B> for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
} // verus!
