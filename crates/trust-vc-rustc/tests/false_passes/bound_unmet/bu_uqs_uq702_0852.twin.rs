verus!{
pub trait Tr { } impl Tr for B { } impl Q for B { }
pub trait Q { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
}
pub mod m2 {
use crate::*;
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
}
}
pub trait U {
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
}
pub struct B { pub b: u8 }
impl Q for A { }
pub struct A { pub a: u8 }
impl U for B {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
impl Tr for A { }
} // verus!
