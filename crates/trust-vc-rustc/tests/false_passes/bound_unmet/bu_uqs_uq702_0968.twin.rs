verus!{
impl Tr for A { }
pub trait Q { }
pub proof fn fB() { (B { b: 0 }).lm0(); }
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub struct B { pub b: u8 }
impl Q for B { }
pub struct Z { pub z: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub mod m1 {
use crate::*;
impl Tr for B { }
impl U for A {
    proof fn lm0(&self) { }
}
}
} // verus!
