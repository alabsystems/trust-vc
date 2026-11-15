verus!{
pub struct A { pub a: u8 }
pub trait Q: Tr { }
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Tr + Q { self.lm1(); }
}
impl Q for A { }
pub mod m1 {
use crate::*;
impl U<A> for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
}
pub struct B { pub b: u8 }
pub proof fn fB() { <B as U<B>>::lm0(&(B { b: 0 })); }
impl U<Z> for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub mod m2 {
use crate::*;
impl Tr for B { }
}
impl Tr for A { }
pub proof fn fA() { <A as U<A>>::lm1(&(A { a: 0 })); }
pub struct Z { pub z: u8 }
impl U<B> for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
impl Q for B { }
} // verus!
