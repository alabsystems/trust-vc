verus!{
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
}
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl U for B {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
}
impl Tr for B { }
pub trait Q { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq0(&self) where Self: Q requires self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm1(); }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Q for A { }
} // verus!
