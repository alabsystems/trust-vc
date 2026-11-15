verus!{
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
pub struct B { pub b: u8 }
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Tr for Z { }
pub trait Tr { }
pub mod m2 {
use crate::*;
impl Tr for A { }
}
pub trait Q: Tr { }
pub struct A { pub a: u8 }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl Q for Z { }
} // verus!
