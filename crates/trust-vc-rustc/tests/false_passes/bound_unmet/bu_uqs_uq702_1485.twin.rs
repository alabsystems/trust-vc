verus!{
impl Q for Z { }
pub trait U<T> {
    proof fn rq1(&self) where T: Q requires self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
}
impl Q for A { }
pub struct A { pub a: u8 } impl Tr for B { } impl Q for B { }
pub struct Z { pub z: u8 }
pub trait Q { }
pub struct B { pub b: u8 }
pub trait Tr { }
impl U<B> for Z {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
pub mod m2 {
use crate::*;
impl U<A> for A {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
impl U<Z> for B {
    proof fn rq1(&self) { assert(self.mm() == 2); }
    proof fn lm0(&self) { }
}
}
pub mod m1 {
use crate::*;
impl Tr for Z { }
}
} // verus!
