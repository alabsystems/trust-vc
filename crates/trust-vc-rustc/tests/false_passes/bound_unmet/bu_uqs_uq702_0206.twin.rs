verus!{
pub mod m2 {
use crate::*;
impl Tr for B { }
}
pub trait Tr { }
impl U for B {
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for A { }
pub struct Z { pub z: u8 }
impl U for A {
    proof fn rq1(&self) { assert(self.mm() == 2); }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn rq1(&self) { }
}
impl Q for B { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn rq1(&self) where Self: Q requires self.mm() == 2;
}
pub struct B { pub b: u8 }
pub trait Q { }
pub mod m1 {
use crate::*;
impl Q for A { }
}
} // verus!
