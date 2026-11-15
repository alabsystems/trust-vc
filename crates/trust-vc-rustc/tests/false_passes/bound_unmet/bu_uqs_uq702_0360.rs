verus!{
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where T: Tr { self.z0() }
}
pub struct Z { pub z: u8 }
pub trait Q { }
pub struct A { pub a: u8 }
impl Q for B { }
pub struct B { pub b: u8 }
impl Tr for A { }
impl Tr for Z { }
pub trait Tr { }
impl Q for Z { }
pub mod m1 {
use crate::*;
impl U<A> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
}
impl U<Z> for B {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U<B> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl Q for A { }
} // verus!
