verus!{
impl Tr for B { }
pub trait Q { } impl Tr for A { }
pub trait Tr { }
pub struct A { pub a: u8 }
pub mod m2 {
use crate::*;
impl U<B> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
}
impl Q for A { }
impl U<Z> for B {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
impl U<A> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
} // verus!
