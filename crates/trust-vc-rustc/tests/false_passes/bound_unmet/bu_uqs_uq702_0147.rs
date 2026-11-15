verus!{
pub trait Tr { }
impl U<Z> for A {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
pub proof fn fA() { <A as U<Z>>::lm0(&(A { a: 0 })); }
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl U<A> for Z {
    proof fn lm0(&self) { }
}
}
impl Q for Z { }
impl Tr for A { }
pub struct A { pub a: u8 }
} // verus!
