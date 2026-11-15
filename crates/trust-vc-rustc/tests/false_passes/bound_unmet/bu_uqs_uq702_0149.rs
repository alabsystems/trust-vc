verus!{
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
}
impl Q for Z { }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Q for B { }
impl Q for A { }
pub mod m1 {
use crate::*;
impl Tr for B { }
}
pub trait Q { }
impl U<A> for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
impl U<B> for B {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
impl U<Z> for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
} // verus!
