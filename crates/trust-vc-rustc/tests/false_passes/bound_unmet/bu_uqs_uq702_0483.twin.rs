verus!{
pub struct A { pub a: u8 } impl Tr for Z { }
pub trait Q { }
impl Q for Z { }
pub trait Tr { }
pub trait U {
    proof fn dd(&self) where Self: Tr + Q { self.lm1(); }
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl U for A {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct Z { pub z: u8 }
impl U for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub mod m2 {
use crate::*;
impl Q for A { }
}
pub struct B { pub b: u8 }
} // verus!
