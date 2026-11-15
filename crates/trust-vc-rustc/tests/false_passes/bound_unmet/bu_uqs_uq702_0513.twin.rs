verus!{
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl Q for A { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn rq1(&self) where Self: Tr + Q requires self.mm() == 2;
}
impl Tr for B { }
impl U for B {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
pub trait Q { }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl U for A {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
}
} // verus!
