verus!{
pub trait Q { }
pub struct B { pub b: u8 }
pub proof fn fA() { (A { a: 0 }).lm1(); }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub mod m1 {
use crate::*;
impl Q for A { }
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
