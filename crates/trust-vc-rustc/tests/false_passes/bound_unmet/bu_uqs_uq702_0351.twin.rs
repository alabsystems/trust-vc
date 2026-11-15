verus!{
impl Tr for A { }
impl Tr for Z { }
pub struct A { pub a: u8 } impl Q for Z { }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub mod m1 {
use crate::*;
impl Q for A { }
}
pub trait U {
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
}
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
