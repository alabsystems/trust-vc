verus!{
pub struct B { pub b: u8 }
pub trait Tr { }
impl Tr for A { }
pub mod m2 {
use crate::*;
impl U<Z> for Z {
    proof fn lm0(&self) { }
}
}
pub struct A { pub a: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    proof fn dd(&self) where T: Tr { self.lm0(); }
}
impl U<A> for B {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub trait Q { }
impl U<A> for A {
    proof fn lm0(&self) { }
}
impl Q for A { }
} // verus!
