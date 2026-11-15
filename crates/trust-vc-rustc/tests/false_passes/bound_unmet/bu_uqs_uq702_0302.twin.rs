verus!{
pub trait Tr { }
pub struct B { pub b: u8 }
impl U<Z> for Z {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
impl U<A> for B {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
impl U<B> for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
impl Tr for Z { }
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl Q for Z { }
}
pub struct Z { pub z: u8 }
pub trait Q: Tr { }
pub trait U<T> {
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq0(&self) where T: Tr requires self.mm() == 2;
}
impl Q for B { }
impl Tr for B { }
} // verus!
