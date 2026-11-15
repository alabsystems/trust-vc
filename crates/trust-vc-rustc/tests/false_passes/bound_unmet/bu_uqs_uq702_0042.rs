verus!{
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl U<A> for B {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where T: Q ensures r == self.mm();
}
impl Tr for Z { }
pub mod m2 {
use crate::*;
impl U<A> for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait Q: Tr { }
pub struct A { pub a: u8 }
impl Q for A { }
impl Tr for A { }
pub fn fB() { let _r = <B as U<A>>::z0(&(B { b: 0 })); }
impl U<Z> for Z {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
} // verus!
