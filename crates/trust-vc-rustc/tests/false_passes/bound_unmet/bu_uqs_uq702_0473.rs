verus!{
pub mod m1 {
use crate::*;
impl Q for Z { }
}
impl U<B> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Q for A { }
impl Tr for Z { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
}
impl U<Z> for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub trait Q: Tr { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl Tr for A { }
pub struct B { pub b: u8 }
impl Tr for B { }
impl U<A> for A {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
} // verus!
