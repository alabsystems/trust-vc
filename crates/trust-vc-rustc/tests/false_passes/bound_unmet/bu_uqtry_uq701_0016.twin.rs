verus!{
pub trait Q { } impl Tr for Z { } impl Q for Z { }
pub struct A { pub a: u8 }
impl Tr for B { }
pub struct Z { pub z: u8 }
pub struct B { pub b: u8 }
pub trait U<T> {
    proof fn lm1(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Tr + Q { self.lm1(); }
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
}
pub mod m2 {
use crate::*;
impl U<Z> for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
}
pub trait Tr { }
impl U<B> for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
} // verus!
