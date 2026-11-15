verus!{
pub struct A { pub a: u8 }
pub trait Q { }
pub struct B { pub b: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
}
impl U<A> for B {
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub mod m1 {
use crate::*;
impl U<A> for Z {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
}
impl Tr for A { }
pub struct Z { pub z: u8 }
pub mod m2 {
use crate::*;
impl U<Z> for A {
    proof fn lm0(&self) { }
}
}
} // verus!
