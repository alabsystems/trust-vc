verus!{
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait Tr { }
pub trait U {
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn rq0(&self) where Self: Q requires self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
pub mod m2 {
use crate::*;
impl Q for B { }
}
pub struct A { pub a: u8 }
impl U for B {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for A { }
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
pub struct B { pub b: u8 }
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
} // verus!
