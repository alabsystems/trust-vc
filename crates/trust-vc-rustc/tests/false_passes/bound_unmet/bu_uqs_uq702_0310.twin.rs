verus!{
impl U<Z> for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait Tr { }
impl U<A> for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub proof fn fB() { <B as U<Z>>::lm1(&(B { b: 0 })); }
pub mod m1 {
use crate::*;
impl Tr for Z { }
}
impl U<Z> for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
impl Q for Z { }
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Q ensures self.mm() == 2;
}
pub struct A { pub a: u8 }
impl Tr for A { }
} // verus!
