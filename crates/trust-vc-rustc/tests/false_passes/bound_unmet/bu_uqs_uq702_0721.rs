verus!{
pub mod m1 {
use crate::*;
impl Q for B { }
impl U for B {
    proof fn rq0(&self) { assert(self.mm() == 2); }
    proof fn lm1(&self) { }
}
}
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm1(); }
}
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
impl U for Z {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
impl Tr for B { }
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub trait Tr { }
pub struct A { pub a: u8 }
} // verus!
