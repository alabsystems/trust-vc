verus!{
impl Tr for A { }
pub mod m1 {
use crate::*;
impl Q for Z { }
}
pub struct Z { pub z: u8 }
impl U for B {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
impl Q for B { }
impl U for A {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2;
}
impl Q for A { }
impl Tr for B { }
pub trait Tr { }
impl U for Z {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
} // verus!
