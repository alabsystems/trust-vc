verus!{
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
impl Tr for B { }
impl Q for Z { }
pub trait Tr { }
pub trait Q: Tr { }
pub mod m2 {
use crate::*;
impl Q for B { }
}
pub struct A { pub a: u8 }
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl U for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl U for A {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for Z { }
} // verus!
