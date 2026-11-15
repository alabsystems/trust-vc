verus!{
pub trait Tr { }
pub trait Q: Tr { }
impl Q for A { }
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
}
}
pub struct B { pub b: u8 }
impl Tr for A { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
impl Tr for B { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm0(); }
}
impl U for A {
    proof fn lm0(&self) { }
}
impl U for B {
    proof fn lm0(&self) { }
}
} // verus!
