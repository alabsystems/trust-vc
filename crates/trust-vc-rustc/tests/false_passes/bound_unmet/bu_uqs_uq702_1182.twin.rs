verus!{
pub trait Tr { } impl Tr for A { } impl Q for A { }
pub trait Q: Tr { }
impl U for B {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm1(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm0(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Tr + Q { self.lm1(); }
}
impl Tr for B { }
pub struct Z { pub z: u8 }
impl U for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct A { pub a: u8 }
impl U for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub mod m2 {
use crate::*;
impl Q for B { }
}
impl Tr for Z { }
pub struct B { pub b: u8 }
} // verus!
