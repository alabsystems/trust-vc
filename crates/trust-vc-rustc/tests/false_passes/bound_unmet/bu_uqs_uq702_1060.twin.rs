verus!{
pub trait Q: Tr { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl U<Z> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub fn fA() { let _r = <A as U<A>>::z0(&(A { a: 0 })); }
pub struct A { pub a: u8 }
impl Tr for A { }
pub fn fB() { let _r = <B as U<B>>::z0(&(B { b: 0 })); }
impl Q for B { }
impl Tr for B { }
impl U<A> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U<T> {
    fn z0(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 { 2 }
}
impl Q for A { }
impl U<B> for B {
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
