verus!{
pub mod m2 {
use crate::*;
impl U<A> for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
}
impl Q for Z { }
pub struct Z { pub z: u8 }
impl Tr for A { }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait U<T> {
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
pub mod m1 {
use crate::*;
impl U<Z> for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl Tr for Z { }
}
pub proof fn fA() { <A as U<Z>>::lm0(&(A { a: 0 })); }
pub trait Q { }
pub trait Tr { }
} // verus!
