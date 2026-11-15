verus!{
pub trait Tr { }
impl Tr for B { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Q { self.lm0(); }
}
impl Q for A { }
pub struct B { pub b: u8 }
pub trait Q { }
impl U<B> for Z {
    proof fn lm0(&self) { }
}
impl Tr for A { }
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl U<A> for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
}
pub struct A { pub a: u8 }
impl U<B> for B {
    proof fn lm0(&self) { }
}
} // verus!
