verus!{
impl U<Z> for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub proof fn fA() { <A as U<Z>>::lm0(&(A { a: 0 })); }
pub trait U<T> {
    proof fn dd(&self) where T: Tr { self.lm1(); }
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
pub trait Q { }
pub mod m2 {
use crate::*;
impl U<Z> for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
}
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
impl U<B> for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Tr { }
impl Tr for Z { }
pub struct A { pub a: u8 }
} // verus!
