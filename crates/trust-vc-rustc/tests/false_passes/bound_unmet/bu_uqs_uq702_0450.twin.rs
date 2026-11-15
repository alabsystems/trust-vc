verus!{
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl Tr for Z { }
impl U<B> for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
}
pub struct A { pub a: u8 }
pub trait Q { }
pub mod m1 {
use crate::*;
impl U<Z> for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
}
pub struct B { pub b: u8 }
impl Q for Z { }
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dd(&self) where T: Tr { self.lm0(); }
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
} // verus!
