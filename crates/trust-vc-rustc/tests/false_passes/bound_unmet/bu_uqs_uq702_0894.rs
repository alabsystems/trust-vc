verus!{
pub struct Z { pub z: u8 }
impl U for A {
    proof fn lm0(&self) { }
}
impl U for Z {
    proof fn lm0(&self) { }
}
impl Tr for Z { }
impl Tr for B { }
pub trait Q { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
impl Q for Z { }
impl Q for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub trait Tr { }
pub mod m2 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
}
}
} // verus!
