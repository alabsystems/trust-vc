verus!{
pub trait Q { }
impl Q for B { }
pub struct B { pub b: u8 }
impl Tr for Z { }
impl Tr for B { }
impl Q for Z { }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for A { }
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm1(); }
}
} // verus!
