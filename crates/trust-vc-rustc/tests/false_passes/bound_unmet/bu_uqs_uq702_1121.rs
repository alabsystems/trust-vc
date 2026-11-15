verus!{
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl Tr for A { }
pub struct Z { pub z: u8 }
pub trait Q: Tr { }
pub struct A { pub a: u8 }
impl Q for Z { }
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait Tr { }
} // verus!
