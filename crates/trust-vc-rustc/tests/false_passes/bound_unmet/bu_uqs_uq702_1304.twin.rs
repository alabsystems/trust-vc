verus!{
impl Tr for A { }
pub mod m2 {
use crate::*;
impl Tr for B { }
}
pub struct B { pub b: u8 } impl Q for A { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
}
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for B { }
pub trait Tr { }
impl U for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Q { }
} // verus!
