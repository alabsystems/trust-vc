verus!{
impl Tr for A { }
impl Q for A { }
pub trait U {
    proof fn dd(&self) where Self: Q { self.lm0(); }
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
}
pub trait Q: Tr { }
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub mod m2 {
use crate::*;
impl Tr for Z { }
}
impl Tr for B { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
} // verus!
