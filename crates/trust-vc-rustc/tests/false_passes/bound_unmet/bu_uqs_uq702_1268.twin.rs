verus!{
pub trait Tr { }
impl Q for A { }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
impl Q for Z { }
impl Tr for A { }
pub mod m2 {
use crate::*;
impl Q for B { }
}
pub struct Z { pub z: u8 }
impl Tr for B { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub mod m1 {
use crate::*;
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
pub trait Q { }
pub proof fn fB() { (B { b: 0 }).lm0(); }
} // verus!
