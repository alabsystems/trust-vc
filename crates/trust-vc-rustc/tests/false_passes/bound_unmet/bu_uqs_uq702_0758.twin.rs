verus!{
pub fn fA() { let _r = <A as U<B>>::z0(&(A { a: 0 })); }
pub fn fB() { let _r = <B as U<B>>::z0(&(B { b: 0 })); }
impl U<B> for B {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q: Tr { }
pub struct B { pub b: u8 }
impl Tr for B { }
pub mod m2 {
use crate::*;
impl U<A> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U<B> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl Q for B { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
    fn dd(&self) -> (r: u8) where T: Tr + Q { self.z0() }
}
pub trait Tr { }
} // verus!
