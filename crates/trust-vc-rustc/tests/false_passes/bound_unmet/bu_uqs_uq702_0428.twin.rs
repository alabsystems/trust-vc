verus!{
pub mod m1 {
use crate::*;
impl U<B> for B {
    fn z0(&self) -> (r: u8) { 2 }
}
impl U<B> for Z {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
}
impl U<Z> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl Q for B { }
pub struct B { pub b: u8 }
pub trait U<T> {
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 { 2 }
}
pub mod m2 {
use crate::*;
impl Q for Z { }
}
pub trait Tr { }
pub fn fB() { let _r = <B as U<B>>::z0(&(B { b: 0 })); }
impl Tr for B { }
} // verus!
