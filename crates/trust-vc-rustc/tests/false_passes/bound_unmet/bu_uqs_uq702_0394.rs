verus!{
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl Q for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    fn dd(&self) -> (r: u8) where Self: Tr { self.z0() }
}
pub trait Q { }
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait Tr { }
pub struct Z { pub z: u8 }
} // verus!
