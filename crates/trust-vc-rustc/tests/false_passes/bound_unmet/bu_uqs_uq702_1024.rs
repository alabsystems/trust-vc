verus!{
pub trait Tr { }
pub mod m1 {
use crate::*;
impl Tr for A { }
}
impl U for B {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
impl Q for A { }
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
pub struct Z { pub z: u8 }
impl Tr for B { }
pub struct A { pub a: u8 }
pub trait U {
    proof fn rq0(&self) where Self: Q requires self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
pub trait Q { }
pub struct B { pub b: u8 }
} // verus!
