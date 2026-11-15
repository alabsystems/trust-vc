verus!{
pub trait Tr { } impl Q for Z { }
pub mod m1 {
use crate::*;
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
}
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub mod m2 {
use crate::*;
impl Tr for A { }
}
pub trait U {
    proof fn dd(&self) where Self: Q { self.lm1(); }
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
}
impl U for B {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
pub struct A { pub a: u8 }
impl Q for A { }
impl Tr for B { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl Tr for Z { }
} // verus!
