verus!{
pub proof fn fB() { <B as U<B>>::lm0(&(B { b: 0 })); }
pub trait Q: Tr { }
pub struct B { pub b: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
}
pub struct A { pub a: u8 }
impl Q for B { }
impl U<A> for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub mod m1 {
use crate::*;
impl Tr for B { }
}
pub struct Z { pub z: u8 }
pub proof fn fA() { <A as U<B>>::lm1(&(A { a: 0 })); }
impl U<B> for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub mod m2 {
use crate::*;
impl U<B> for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
}
} // verus!
