verus!{
pub struct A { pub a: u8 }
pub trait Tr { }
impl U<A> for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
impl U<Z> for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl Tr for A { }
}
pub trait Q: Tr { }
pub struct B { pub b: u8 }
impl Q for A { }
impl Tr for Z { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where T: Q ensures r == self.mm();
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
}
} // verus!
