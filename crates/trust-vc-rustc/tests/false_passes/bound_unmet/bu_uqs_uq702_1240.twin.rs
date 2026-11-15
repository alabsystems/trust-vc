verus!{
impl Q for A { }
pub trait Tr { }
impl U<Z> for B {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl U<B> for Z {
    proof fn lm0(&self) { }
}
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
impl Tr for Z { }
impl U<A> for A {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q: Tr { }
impl Tr for B { }
impl Tr for A { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
} // verus!
