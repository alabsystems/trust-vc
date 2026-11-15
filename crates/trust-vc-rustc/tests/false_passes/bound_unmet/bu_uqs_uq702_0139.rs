verus!{
impl Tr for A { }
pub trait Tr { }
impl U<A> for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
impl Q for A { }
pub mod m2 {
use crate::*;
impl U<A> for B {
    proof fn lm0(&self) { }
}
}
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub proof fn fA() { <A as U<A>>::lm0(&(A { a: 0 })); }
impl U<Z> for Z {
    proof fn lm0(&self) { }
}
pub trait Q { }
pub struct B { pub b: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Q { self.lm0(); }
}
} // verus!
