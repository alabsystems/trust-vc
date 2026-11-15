verus!{
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub mod m1 {
use crate::*;
impl Tr for A { }
}
pub trait Tr { }
pub struct A { pub a: u8 }
pub fn fA() { let _r = (A { a: 0 }).z1(); }
pub struct B { pub b: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    proof fn dd(&self) where Self: Tr + Q { self.lm0(); }
}
impl Q for A { }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
} // verus!
