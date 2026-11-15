verus!{
impl Tr for Z { }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub mod m1 {
use crate::*;
impl Q for A { }
}
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub trait U {
    proof fn dd(&self) where Self: Tr { self.lm0(); }
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Q { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
} // verus!
