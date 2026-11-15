verus!{
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub mod m2 {
use crate::*;
impl Tr for Z { }
impl Tr for B { }
}
pub struct Z { pub z: u8 }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait Q: Tr { }
pub struct A { pub a: u8 }
impl U for B {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
impl Tr for A { }
pub trait U {
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
}
} // verus!
