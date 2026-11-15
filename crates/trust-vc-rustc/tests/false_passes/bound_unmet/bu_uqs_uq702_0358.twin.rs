verus!{
pub trait Tr { } impl Tr for A { } impl Q for A { }
pub trait U {
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn rq0(&self) { }
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl Q for Z { }
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn rq0(&self) { assert(self.mm() == 2); }
    fn z1(&self) -> (r: u8) { 2 }
}
}
impl Tr for Z { }
} // verus!
