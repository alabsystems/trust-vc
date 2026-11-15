verus!{
pub struct B { pub b: u8 }
pub mod m1 {
use crate::*;
impl U for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Tr for B { }
impl Q for A { }
}
pub trait Q { }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
impl Q for Z { }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr + Q { self.lm1(); }
}
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
