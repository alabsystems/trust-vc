verus!{
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub struct B { pub b: u8 }
impl Tr for B { }
pub mod m2 {
use crate::*;
impl Q for Z { }
}
impl Q for B { }
pub struct A { pub a: u8 }
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
impl U for B {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
impl Q for A { }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl Tr for A { }
pub proof fn fA() { (A { a: 0 }).lm0(); }
} // verus!
