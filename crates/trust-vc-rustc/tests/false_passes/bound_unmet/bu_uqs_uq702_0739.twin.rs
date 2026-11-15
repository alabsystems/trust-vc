verus!{
pub struct B { pub b: u8 } impl Tr for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2;
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub struct A { pub a: u8 }
impl Q for A { }
impl U for Z {
    proof fn rq1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
impl Tr for Z { }
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl U for A {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
}
pub trait Tr { }
pub trait Q { }
} // verus!
