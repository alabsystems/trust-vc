verus!{
impl U<A> for B {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub mod m1 {
use crate::*;
impl U<B> for Z {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
}
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl Tr for A { }
}
pub fn fA() { let _r = <A as U<A>>::z1(&(A { a: 0 })); }
pub struct A { pub a: u8 }
pub trait Q: Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
    fn dd(&self) -> (r: u8) where T: Tr + Q { self.z1() }
}
impl U<A> for A {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
impl Q for A { }
pub trait Tr { }
pub fn fB() { let _r = <B as U<A>>::z0(&(B { b: 0 })); }
} // verus!
