verus!{
pub struct A { pub a: u8 }
impl U<B> for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
pub mod m2 {
use crate::*;
impl Tr for Z { }
impl Q for Z { }
impl Tr for B { }
impl Tr for A { }
}
pub trait U<T> {
    proof fn dd(&self) where T: Tr + Q { self.lm1(); }
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm1(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
}
impl U<Z> for B {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl U<A> for A {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct Z { pub z: u8 }
pub trait Q { }
pub struct B { pub b: u8 }
pub trait Tr { }
} // verus!
