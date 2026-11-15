verus!{
pub trait Q { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
impl U<A> for B {
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl U<B> for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
impl Q for B { }
pub trait U<T> {
    proof fn rq1(&self) where T: Q requires self.mm() == 2;
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 { 2 }
}
impl Tr for B { }
impl Tr for A { }
pub struct A { pub a: u8 }
pub trait Tr { }
pub mod m2 {
use crate::*;
impl U<B> for Z {
    proof fn rq1(&self) { assert(self.mm() == 2); }
    fn z0(&self) -> (r: u8) { 2 }
}
}
} // verus!
