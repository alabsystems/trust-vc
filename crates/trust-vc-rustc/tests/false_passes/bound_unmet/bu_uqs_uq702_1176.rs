verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl Tr for B { }
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Tr for Z { }
}
pub struct A { pub a: u8 }
pub trait Q { }
pub trait Tr { }
impl U for B {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl Q for Z { }
}
} // verus!
