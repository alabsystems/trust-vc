verus!{
pub struct Z { pub z: u8 } impl Q for A { }
pub trait U<T> {
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Q { self.lm1(); }
    open spec fn mm(&self) -> u8 where T: Q { 2 }
}
impl Tr for A { }
impl Q for Z { }
pub mod m2 {
use crate::*;
impl U<A> for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
}
pub struct A { pub a: u8 }
pub trait Tr { }
pub trait Q: Tr { }
pub struct B { pub b: u8 }
impl Tr for Z { }
impl U<Z> for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
