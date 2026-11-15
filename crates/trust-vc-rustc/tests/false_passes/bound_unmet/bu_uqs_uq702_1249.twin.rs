verus!{
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
}
pub struct A { pub a: u8 }
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
pub trait Q { }
impl Q for A { }
pub mod m2 {
use crate::*;
impl Tr for A { }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
} // verus!
