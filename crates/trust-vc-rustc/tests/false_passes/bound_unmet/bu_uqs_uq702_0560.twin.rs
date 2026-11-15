verus!{
impl Q for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq0(&self) where Self: Tr + Q requires self.mm() == 2;
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub struct Z { pub z: u8 }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm1(&self) { }
    proof fn rq0(&self) { }
}
}
impl Tr for A { }
impl U for Z {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub trait Q { }
impl U for B {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
pub struct A { pub a: u8 }
} // verus!
