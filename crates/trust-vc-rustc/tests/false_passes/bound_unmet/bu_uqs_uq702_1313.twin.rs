verus!{
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm0(&self) { }
}
pub trait U {
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
impl U for A {
    proof fn lm0(&self) { }
}
pub struct A { pub a: u8 }
impl Q for B { }
pub mod m2 {
use crate::*;
impl Tr for B { }
}
pub trait Tr { }
impl Tr for A { }
} // verus!
