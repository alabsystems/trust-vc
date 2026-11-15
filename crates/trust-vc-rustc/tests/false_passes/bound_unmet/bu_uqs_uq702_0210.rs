verus!{
impl Q for Z { }
pub struct A { pub a: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm1(); }
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for A { }
impl Tr for B { }
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl Tr for Z { }
}
impl Tr for A { }
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
