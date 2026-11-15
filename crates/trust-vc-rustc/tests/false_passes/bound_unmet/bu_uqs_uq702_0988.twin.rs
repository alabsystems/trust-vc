verus!{
pub struct B { pub b: u8 }
pub trait Q { }
pub struct A { pub a: u8 }
pub trait Tr { }
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl Tr for A { }
impl Q for B { }
}
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub struct Z { pub z: u8 }
} // verus!
