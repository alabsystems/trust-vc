verus!{
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Tr + Q { self.lm0(); }
}
pub struct A { pub a: u8 }
impl Tr for B { }
pub trait Q { }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl U<B> for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for A { }
}
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl Q for A { }
pub proof fn fB() { <B as U<A>>::lm1(&(B { b: 0 })); }
impl U<A> for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
