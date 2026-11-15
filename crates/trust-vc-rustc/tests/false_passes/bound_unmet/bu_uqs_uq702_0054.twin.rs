verus!{
pub mod m1 {
use crate::*;
impl U<Z> for B {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
}
pub struct Z { pub z: u8 }
pub trait U<T> {
    proof fn rq1(&self) where T: Tr requires self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
impl Q for Z { }
pub trait Tr { }
impl U<Z> for A {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
pub struct A { pub a: u8 }
pub trait Q: Tr { }
impl Tr for Z { }
impl U<B> for Z {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
} // verus!
