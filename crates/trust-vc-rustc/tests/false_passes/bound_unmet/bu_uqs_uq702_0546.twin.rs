verus!{
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for Z { }
pub trait Q { }
pub trait Tr { }
pub mod m2 {
use crate::*;
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
}
impl Q for B { }
impl Q for A { }
} // verus!
