verus!{
impl Q for Z { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
pub struct Z { pub z: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn rq1(&self) where Self: Q requires self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
impl Tr for B { }
pub trait Tr { }
pub trait Q { }
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl Q for A { }
}
pub mod m2 {
use crate::*;
impl U for Z {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
}
pub struct A { pub a: u8 }
} // verus!
