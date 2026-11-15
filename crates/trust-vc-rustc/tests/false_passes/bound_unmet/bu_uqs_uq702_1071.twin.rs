verus!{
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub mod m2 {
use crate::*;
impl Q for A { }
impl Tr for A { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for Z { }
}
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
}
pub trait Q { }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Tr for B { }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
} // verus!
