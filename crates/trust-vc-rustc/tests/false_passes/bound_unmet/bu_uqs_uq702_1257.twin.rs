verus!{
pub struct Z { pub z: u8 }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
pub trait Tr { }
impl Q for Z { }
impl Q for A { }
pub trait Q { }
pub struct A { pub a: u8 }
impl Tr for A { }
pub proof fn fA() { (A { a: 0 }).lm0(); }
pub mod m2 {
use crate::*;
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
}
pub struct B { pub b: u8 }
} // verus!
