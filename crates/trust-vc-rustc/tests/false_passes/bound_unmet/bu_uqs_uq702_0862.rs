verus!{
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub trait Q { }
pub struct B { pub b: u8 }
pub proof fn fA() { <A as U<Z>>::lm1(&(A { a: 0 })); }
impl U<Z> for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn rq0(&self) where T: Tr requires self.mm() == 2;
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
}
impl Tr for Z { }
pub mod m1 {
use crate::*;
impl U<B> for Z {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
}
} // verus!
