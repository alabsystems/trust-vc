verus!{
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    proof fn dd(&self) where T: Tr { self.lm0(); }
}
pub proof fn fZ() { <Z as U<A>>::lm0(&(Z { z: 0 })); }
impl U<B> for A {
    proof fn lm0(&self) { }
}
impl Tr for A { }
impl Q for A { }
pub trait Q { }
pub trait Tr { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
impl U<A> for Z {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct A { pub a: u8 }
pub mod m2 {
use crate::*;
impl Q for B { }
}
} // verus!
