verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2;
}
pub trait Tr { } impl Tr for A { } impl Q for A { }
impl U for Z {
    proof fn rq1(&self) { assert(self.mm() == 2); }
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub trait Q: Tr { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl Q for Z { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn rq1(&self) { }
}
pub mod m1 {
use crate::*;
impl Tr for Z { }
}
} // verus!
