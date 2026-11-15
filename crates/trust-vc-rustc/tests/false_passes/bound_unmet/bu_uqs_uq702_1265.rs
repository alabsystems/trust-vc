verus!{
impl Tr for B { }
pub trait U<T> {
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
}
pub struct Z { pub z: u8 }
pub mod m1 {
use crate::*;
impl Tr for Z { }
}
pub struct A { pub a: u8 }
impl U<B> for B {
    proof fn lm0(&self) { }
}
impl U<Z> for A {
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub trait Q { }
pub struct B { pub b: u8 }
} // verus!
