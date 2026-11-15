verus!{
pub trait Q { } impl Q for Z { }
impl Tr for B { }
pub struct B { pub b: u8 }
impl U<B> for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Tr { }
impl U<Z> for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl Q for B { }
pub trait U<T> {
    proof fn dd(&self) where T: Q { self.lm0(); }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Q { 2 }
}
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub mod m1 {
use crate::*;
impl Tr for Z { }
}
} // verus!
