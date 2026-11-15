verus!{
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Tr for A { }
impl U for B {
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub struct B { pub b: u8 }
impl Q for A { }
impl Q for B { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait Q: Tr { }
pub proof fn fB() { (B { b: 0 }).lm0(); }
pub mod m2 {
use crate::*;
impl Tr for B { }
impl U for A {
    proof fn lm0(&self) { }
}
}
impl Tr for Z { }
} // verus!
