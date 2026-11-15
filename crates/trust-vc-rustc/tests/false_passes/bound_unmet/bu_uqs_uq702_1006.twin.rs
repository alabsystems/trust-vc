verus!{
impl Q for B { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
impl Tr for A { }
pub mod m1 {
use crate::*;
impl Q for A { }
}
pub struct B { pub b: u8 }
impl Tr for B { }
pub struct Z { pub z: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
pub trait Tr { }
impl U for B {
    proof fn lm0(&self) { }
}
pub trait Q: Tr { }
} // verus!
