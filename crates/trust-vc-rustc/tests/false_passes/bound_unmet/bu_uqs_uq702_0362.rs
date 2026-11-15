verus!{
pub struct B { pub b: u8 }
impl Tr for Z { }
pub proof fn fZ() { <Z as U<Z>>::lm0(&(Z { z: 0 })); }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn rq1(&self) where T: Tr + Q requires self.mm() == 2;
}
pub mod m2 {
use crate::*;
impl Tr for B { }
impl U<B> for B {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
}
pub struct Z { pub z: u8 }
impl U<Z> for A {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
impl Q for Z { }
pub struct A { pub a: u8 }
pub trait Q { }
pub trait Tr { }
impl U<Z> for Z {
    proof fn rq1(&self) { assert(self.mm() == 2); }
    proof fn lm0(&self) { }
}
} // verus!
