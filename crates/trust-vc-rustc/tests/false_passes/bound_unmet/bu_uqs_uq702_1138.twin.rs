verus!{
impl Q for Z { }
impl Tr for Z { }
pub mod m1 {
use crate::*;
impl Q for A { }
}
pub struct Z { pub z: u8 } impl Tr for B { } impl Q for B { }
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl U for A {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl U for B {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub trait Q: Tr { }
pub fn fZ() { let _r = (Z { z: 0 }).z1(); }
impl Tr for A { }
} // verus!
