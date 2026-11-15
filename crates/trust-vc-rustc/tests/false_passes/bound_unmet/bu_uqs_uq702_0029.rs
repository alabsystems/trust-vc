verus!{
pub struct A { pub a: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn dd(&self) where T: Tr { self.lm0(); }
    proof fn lm1(&self) where T: Tr ensures self.mm() == 2;
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
}
pub trait Tr { }
impl U<B> for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
pub mod m1 {
use crate::*;
impl Tr for A { }
}
impl U<A> for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
