verus!{
pub trait Tr { }
impl U for A {
    proof fn lm0(&self) { }
}
impl Tr for B { }
pub trait Q { }
impl Q for A { }
pub struct B { pub b: u8 }
impl U for Z {
    proof fn lm0(&self) { }
}
pub mod m2 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
}
}
pub struct A { pub a: u8 }
impl Q for B { }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
pub struct Z { pub z: u8 }
} // verus!
