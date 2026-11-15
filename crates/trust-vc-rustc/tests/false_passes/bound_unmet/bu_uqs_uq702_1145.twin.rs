verus!{
pub struct Z { pub z: u8 }
impl Q for B { }
pub struct A { pub a: u8 }
impl U<A> for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for A { }
impl U<Z> for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait U<T> {
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
impl U<B> for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait Q { }
pub mod m1 {
use crate::*;
impl Q for Z { }
}
pub trait Tr { }
pub struct B { pub b: u8 }
impl Q for A { }
} // verus!
