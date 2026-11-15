verus!{
impl Tr for A { }
pub trait Q { }
impl U for A {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for Z { }
}
pub struct B { pub b: u8 }
impl Q for A { }
pub struct A { pub a: u8 }
pub trait Tr { }
pub struct Z { pub z: u8 }
} // verus!
