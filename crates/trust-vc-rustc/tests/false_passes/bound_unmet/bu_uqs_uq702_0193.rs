verus!{
impl U<Z> for A {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl U<Z> for B {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl Q for Z { }
pub struct B { pub b: u8 }
pub trait Q { }
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
pub proof fn fB() { <B as U<Z>>::lm0(&(B { b: 0 })); }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
}
pub trait Tr { }
impl U<B> for Z {
    proof fn lm0(&self) { }
}
} // verus!
