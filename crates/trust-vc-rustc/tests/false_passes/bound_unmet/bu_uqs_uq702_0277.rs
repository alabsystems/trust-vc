verus!{
impl Q for Z { }
pub struct Z { pub z: u8 }
impl Q for A { }
pub struct A { pub a: u8 }
pub trait U<T> {
    proof fn rq1(&self) where T: Tr + Q requires self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
}
pub struct B { pub b: u8 }
impl U<B> for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
pub trait Q { }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl U<Z> for B {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
}
pub mod m2 {
use crate::*;
impl Tr for B { }
impl U<A> for Z {
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
}
} // verus!
