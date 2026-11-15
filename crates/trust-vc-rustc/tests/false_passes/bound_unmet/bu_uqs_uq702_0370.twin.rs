verus!{
impl Q for B { }
impl Tr for A { }
pub struct A { pub a: u8 } impl Tr for Z { } impl Q for Z { }
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
}
}
pub struct B { pub b: u8 }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub trait Q: Tr { }
impl U for A {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
impl Tr for B { }
impl U for B {
    proof fn lm0(&self) { }
}
} // verus!
