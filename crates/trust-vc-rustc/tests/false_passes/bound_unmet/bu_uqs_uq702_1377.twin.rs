verus!{
pub struct A { pub a: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
}
pub mod m2 {
use crate::*;
impl U<Z> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U<B> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
}
impl Q for B { }
pub struct Z { pub z: u8 }
impl Tr for A { }
impl Tr for Z { }
pub trait Q { }
pub mod m1 {
use crate::*;
impl U<A> for B {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
impl Q for A { }
}
pub trait Tr { }
pub struct B { pub b: u8 }
impl Q for Z { }
} // verus!
