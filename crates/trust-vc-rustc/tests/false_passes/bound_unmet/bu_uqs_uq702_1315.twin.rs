verus!{
impl Tr for Z { }
impl U<Z> for A {
    proof fn lm0(&self) { }
}
pub trait Q: Tr { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl Tr for B { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Q { self.lm0(); }
}
pub trait Tr { }
pub mod m2 {
use crate::*;
impl U<B> for Z {
    proof fn lm0(&self) { }
}
}
impl Q for B { }
} // verus!
