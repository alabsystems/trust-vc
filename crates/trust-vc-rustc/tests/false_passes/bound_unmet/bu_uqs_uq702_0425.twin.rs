verus!{
pub struct A { pub a: u8 } impl Tr for Z { } impl Q for Z { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub mod m1 {
use crate::*;
impl Tr for A { }
}
pub trait Tr { }
pub trait Q { }
impl U for Z {
    proof fn lm0(&self) { }
}
impl Q for A { }
impl U for A {
    proof fn lm0(&self) { }
}
} // verus!
