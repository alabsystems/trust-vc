verus!{
pub struct A { pub a: u8 } impl Q for Z { }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl U for Z {
    proof fn lm0(&self) { }
}
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
}
impl Tr for Z { }
pub trait Q { }
impl Q for A { }
impl U for A {
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
} // verus!
