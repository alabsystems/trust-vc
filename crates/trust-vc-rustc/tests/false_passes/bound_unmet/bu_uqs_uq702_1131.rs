verus!{
pub trait Tr { }
impl Q for A { }
pub mod m2 {
use crate::*;
impl Tr for Z { }
impl U<A> for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
}
pub trait Q { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl U<Z> for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct A { pub a: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
}
} // verus!
