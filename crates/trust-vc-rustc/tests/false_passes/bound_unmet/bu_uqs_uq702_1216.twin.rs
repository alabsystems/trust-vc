verus!{
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
impl Tr for B { }
}
impl Q for Z { }
pub mod m1 {
use crate::*;
impl Tr for A { }
}
pub struct A { pub a: u8 }
impl Q for A { }
impl U for Z {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Tr { }
impl U for B {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn rq1(&self) where Self: Tr + Q requires self.mm() == 2;
}
pub trait Q { }
} // verus!
