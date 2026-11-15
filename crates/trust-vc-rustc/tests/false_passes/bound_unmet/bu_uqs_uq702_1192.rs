verus!{
pub struct A { pub a: u8 }
impl Q for A { }
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub trait U {
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
pub trait Q { }
impl Tr for A { }
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for Z { }
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl Q for B { }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
} // verus!
