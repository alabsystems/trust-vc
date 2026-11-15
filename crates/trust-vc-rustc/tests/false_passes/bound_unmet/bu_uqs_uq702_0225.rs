verus!{
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub struct B { pub b: u8 }
impl U<A> for Z {
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl Q for A { }
}
impl U<Z> for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
} // verus!
