verus!{
impl Tr for B { }
pub mod m2 {
use crate::*;
impl U for B {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
}
impl Q for Z { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
impl Q for B { }
impl Tr for Z { }
pub trait Tr { }
pub struct A { pub a: u8 }
impl U for Z {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for A { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm1(); }
}
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
pub trait Q { }
} // verus!
