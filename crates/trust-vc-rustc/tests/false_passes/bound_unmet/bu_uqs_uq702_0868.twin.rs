verus!{
impl Tr for A { }
impl Q for B { }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl Q for A { }
impl U for B {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
}
pub trait Tr { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl Tr for B { }
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Q { }
} // verus!
