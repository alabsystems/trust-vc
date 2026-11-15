verus!{
pub trait Q { }
pub trait Tr { }
impl U for A {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for Z { }
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl Tr for B { }
impl Q for B { }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm1(); }
}
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
} // verus!
