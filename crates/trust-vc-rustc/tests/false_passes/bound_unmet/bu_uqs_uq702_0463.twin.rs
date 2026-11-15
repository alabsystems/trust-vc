verus!{
impl Q for Z { }
impl Tr for B { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
impl Q for A { }
pub trait U {
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
pub struct A { pub a: u8 } impl Q for B { }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for A { }
}
impl U for B {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Q { }
} // verus!
