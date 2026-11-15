verus!{
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
pub trait Tr { }
pub struct B { pub b: u8 }
impl Q for B { }
impl Tr for B { }
pub fn fA() { let _r = <A as U<B>>::z0(&(A { a: 0 })); }
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl U<B> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub struct Z { pub z: u8 }
impl U<Z> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q: Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
}
} // verus!
