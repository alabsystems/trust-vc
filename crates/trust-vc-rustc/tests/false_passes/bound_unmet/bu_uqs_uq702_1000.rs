verus!{
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub mod m1 {
use crate::*;
impl Tr for Z { }
}
pub trait Q { }
impl Q for A { }
pub trait U {
    proof fn rq1(&self) where Self: Q requires self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
pub trait Tr { }
pub mod m2 {
use crate::*;
impl Tr for A { }
}
impl Tr for B { }
impl U for B {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
impl U for Z {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
impl U for A {
    proof fn rq1(&self) { assert(self.mm() == 2); }
    proof fn lm0(&self) { }
}
impl Q for Z { }
pub struct B { pub b: u8 }
} // verus!
