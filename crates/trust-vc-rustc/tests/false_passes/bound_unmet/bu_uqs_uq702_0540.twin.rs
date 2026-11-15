verus!{
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
}
pub trait Q { }
impl Q for A { }
pub struct B { pub b: u8 }
impl Q for Z { }
pub trait Tr { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
} // verus!
