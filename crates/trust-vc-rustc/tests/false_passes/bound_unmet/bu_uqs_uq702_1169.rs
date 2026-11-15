verus!{
impl Tr for B { }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
}
pub struct A { pub a: u8 }
impl U for B {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Q { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
impl Q for A { }
impl Tr for A { }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn rq1(&self) where Self: Tr + Q requires self.mm() == 2;
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
impl Q for Z { }
} // verus!
