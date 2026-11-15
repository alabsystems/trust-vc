verus!{
pub struct B { pub b: u8 } impl Tr for Z { }
impl Q for Z { }
pub trait Q { }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl Tr for A { }
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
pub struct Z { pub z: u8 }
impl U for Z {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
pub struct A { pub a: u8 }
impl Q for A { }
} // verus!
