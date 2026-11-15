verus!{
impl U<Z> for A {
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl U<B> for B {
    proof fn lm0(&self) { }
}
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
pub struct A { pub a: u8 }
pub trait Tr { }
pub struct B { pub b: u8 }
impl U<Z> for Z {
    proof fn lm0(&self) { }
}
pub trait Q { }
pub proof fn fA() { <A as U<Z>>::lm0(&(A { a: 0 })); }
pub proof fn fZ() { <Z as U<Z>>::lm0(&(Z { z: 0 })); }
impl Tr for Z { }
pub struct Z { pub z: u8 }
} // verus!
