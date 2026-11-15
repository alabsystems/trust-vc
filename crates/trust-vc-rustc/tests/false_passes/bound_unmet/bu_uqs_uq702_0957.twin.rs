verus!{
pub mod m2 {
use crate::*;
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq0(&self) where Self: Q requires self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
}
pub trait Tr { }
pub trait Q { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
pub struct B { pub b: u8 }
impl Tr for A { }
} // verus!
