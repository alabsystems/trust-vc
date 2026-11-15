verus!{
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr { self.z1() }
}
impl Q for Z { }
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl Q for A { }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
}
pub struct Z { pub z: u8 }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl Tr for A { }
}
pub fn fA() { let _r = (A { a: 0 }).z1(); }
pub trait Q { }
pub struct A { pub a: u8 }
} // verus!
