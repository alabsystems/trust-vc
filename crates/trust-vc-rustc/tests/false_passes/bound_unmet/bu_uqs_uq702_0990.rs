verus!{
impl Q for Z { }
pub struct A { pub a: u8 }
impl Q for A { }
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl Tr for B { }
pub trait Tr { }
pub mod m2 {
use crate::*;
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
}
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait U {
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm1(); }
}
pub trait Q { }
pub struct B { pub b: u8 }
} // verus!
