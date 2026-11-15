verus!{
pub trait Tr { }
pub mod m2 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait Q { }
impl Tr for B { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl Tr for A { }
pub struct Z { pub z: u8 }
} // verus!
