verus!{
impl Q for B { }
pub trait U<T> {
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
}
pub mod m1 {
use crate::*;
impl U<B> for B {
    proof fn lm0(&self) { }
}
impl Q for A { }
}
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl U<A> for A {
    proof fn lm0(&self) { }
}
impl Tr for B { }
}
pub struct B { pub b: u8 }
pub proof fn fB() { <B as U<B>>::lm0(&(B { b: 0 })); }
pub trait Q { }
pub trait Tr { }
} // verus!
