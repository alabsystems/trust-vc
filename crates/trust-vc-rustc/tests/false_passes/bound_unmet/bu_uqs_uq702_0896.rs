verus!{
impl Q for B { }
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl Tr for A { }
}
impl Tr for B { }
impl U<A> for Z {
    proof fn lm0(&self) { }
}
impl U<B> for A {
    proof fn lm0(&self) { }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
pub proof fn fA() { <A as U<B>>::lm0(&(A { a: 0 })); }
pub trait Q { }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl U<B> for B {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
} // verus!
