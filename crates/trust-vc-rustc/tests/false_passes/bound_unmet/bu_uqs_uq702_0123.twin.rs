verus!{
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr + Q { self.lm1(); }
}
impl Q for A { }
pub struct A { pub a: u8 }
pub trait Tr { }
pub mod m2 {
use crate::*;
impl Tr for A { }
}
impl Tr for B { }
pub trait Q: Tr { }
impl U for B {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
} // verus!
