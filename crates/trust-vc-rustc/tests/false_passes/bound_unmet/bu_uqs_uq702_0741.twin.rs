verus!{
pub struct A { pub a: u8 } impl Q for B { }
pub struct Z { pub z: u8 }
impl Q for A { }
impl Tr for Z { }
impl U for B {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub fn fA() { let _r = (A { a: 0 }).z1(); }
pub mod m2 {
use crate::*;
impl Q for Z { }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
}
pub trait Q: Tr { }
pub trait U {
    fn dd(&self) -> (r: u8) where Self: Q { self.z1() }
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
pub mod m1 {
use crate::*;
impl Tr for A { }
impl Tr for B { }
}
pub struct B { pub b: u8 }
} // verus!
