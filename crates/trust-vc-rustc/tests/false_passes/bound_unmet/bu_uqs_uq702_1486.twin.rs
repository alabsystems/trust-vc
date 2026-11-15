verus!{
pub trait Q { }
impl U<Z> for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for Z { }
pub trait Tr { }
impl Tr for A { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
}
impl Tr for Z { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub mod m2 {
use crate::*;
impl U<A> for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl U<B> for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
}
impl Tr for B { }
} // verus!
