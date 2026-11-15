verus!{
impl Tr for A { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
pub struct Z { pub z: u8 }
impl Tr for Z { }
impl U<A> for Z {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl U<Z> for A {
    proof fn lm0(&self) { }
}
pub proof fn fA() { <A as U<Z>>::lm0(&(A { a: 0 })); }
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait Q: Tr { }
pub mod m2 {
use crate::*;
impl Q for Z { }
}
} // verus!
