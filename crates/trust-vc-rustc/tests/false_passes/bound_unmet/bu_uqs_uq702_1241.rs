verus!{
pub struct B { pub b: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    proof fn dd(&self) where T: Tr { self.lm0(); }
}
pub trait Tr { }
impl U<A> for Z {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl Tr for B { }
impl Q for A { }
pub mod m2 {
use crate::*;
impl U<B> for A {
    proof fn lm0(&self) { }
}
}
pub struct A { pub a: u8 }
pub trait Q { }
} // verus!
