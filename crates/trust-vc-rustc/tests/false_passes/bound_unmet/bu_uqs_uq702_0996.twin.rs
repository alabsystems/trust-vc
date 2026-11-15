verus!{
impl U for A {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for B { }
impl Q for Z { }
pub proof fn fA() { (A { a: 0 }).lm1(); }
pub trait U {
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 { 2 }
}
pub mod m2 {
use crate::*;
impl Q for B { }
impl U for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait Q { }
pub struct B { pub b: u8 }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl Tr for A { }
}
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
impl Q for A { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
} // verus!
