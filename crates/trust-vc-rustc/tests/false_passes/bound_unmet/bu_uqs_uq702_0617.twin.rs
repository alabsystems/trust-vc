verus!{
pub mod m1 {
use crate::*;
impl U<Z> for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
    proof fn dd(&self) where T: Tr { self.lm0(); }
}
pub trait Q { }
pub struct B { pub b: u8 }
impl U<B> for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl Tr for B { }
pub proof fn fA() { <A as U<B>>::lm0(&(A { a: 0 })); }
impl Q for B { }
} // verus!
