verus!{
pub trait Q { } impl Tr for Z { } impl Q for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn rq0(&self) where Self: Tr + Q requires self.mm() == 2;
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl Tr for B { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub trait Tr { }
pub struct B { pub b: u8 }
impl Q for B { }
impl Q for A { }
pub mod m2 {
use crate::*;
impl U for Z {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
}
impl U for B {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for A { }
impl U for A {
    proof fn rq0(&self) { }
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
} // verus!
