verus!{
impl U for Z {
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl Tr for A { }
}
pub trait Q: Tr { }
impl U for B {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub trait Tr { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
impl Tr for B { }
impl Q for A { }
impl U for A {
    proof fn lm0(&self) { }
}
} // verus!
