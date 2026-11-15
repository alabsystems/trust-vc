verus!{
pub struct A { pub a: u8 }
impl U<B> for B {
    proof fn lm0(&self) { }
}
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
pub struct Z { pub z: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Q { self.lm0(); }
}
impl Q for B { }
impl U<Z> for Z {
    proof fn lm0(&self) { }
}
pub trait Q { }
pub struct B { pub b: u8 }
impl U<Z> for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
pub trait Tr { }
} // verus!
