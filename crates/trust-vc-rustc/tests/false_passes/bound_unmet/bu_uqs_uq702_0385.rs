verus!{
pub trait Tr { }
pub trait Q { }
impl Q for B { }
impl Q for Z { }
pub struct A { pub a: u8 }
pub fn fZ() { let _r = (Z { z: 0 }).z1(); }
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Q for A { }
}
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
}
impl Tr for Z { }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub trait U {
    fn dd(&self) -> (r: u8) where Self: Tr + Q { self.z1() }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    fn z1(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
} // verus!
