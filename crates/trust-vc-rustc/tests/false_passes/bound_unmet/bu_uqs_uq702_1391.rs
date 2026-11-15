verus!{
pub struct Z { pub z: u8 }
impl U<Z> for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl Q for Z { }
impl U<A> for A {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Q { }
pub trait U<T> {
    proof fn dd(&self) where T: Q { self.lm0(); }
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    fn z1(&self) -> (r: u8) where T: Q ensures r == self.mm();
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
pub struct B { pub b: u8 }
pub trait Tr { }
impl Tr for A { }
} // verus!
