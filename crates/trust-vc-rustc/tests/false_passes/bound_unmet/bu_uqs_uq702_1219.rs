verus!{
pub trait Tr { }
impl Tr for A { }
pub struct Z { pub z: u8 }
impl U<A> for B {
    proof fn lm0(&self) { }
}
impl Tr for Z { }
pub struct A { pub a: u8 }
pub trait Q { }
impl U<Z> for Z {
    proof fn lm0(&self) { }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn dd(&self) where T: Q { self.lm0(); }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
pub mod m2 {
use crate::*;
impl U<A> for A {
    proof fn lm0(&self) { }
}
}
impl Q for Z { }
pub struct B { pub b: u8 }
} // verus!
