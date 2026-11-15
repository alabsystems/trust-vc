verus!{
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
pub mod m1 {
use crate::*;
impl U for A {
    proof fn lm0(&self) { }
}
}
pub struct A { pub a: u8 }
impl Tr for A { }
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub trait Q { }
} // verus!
