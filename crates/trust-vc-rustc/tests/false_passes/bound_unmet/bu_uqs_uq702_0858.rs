verus!{
impl U for A {
    proof fn rq0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl U for B {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn rq0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct B { pub b: u8 }
pub trait Tr { }
impl Q for Z { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl Tr for B { }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn rq0(&self) { assert(self.mm() == 2); }
}
}
impl Tr for Z { }
impl Q for B { }
} // verus!
