verus!{
pub trait Tr { }
pub mod m2 {
use crate::*;
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
}
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
impl Q for Z { }
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where Self: Tr { self.z1() }
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl Q for A { }
pub struct Z { pub z: u8 }
} // verus!
