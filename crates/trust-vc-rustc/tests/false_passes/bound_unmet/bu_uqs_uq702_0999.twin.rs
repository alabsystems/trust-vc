verus!{
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
}
pub trait Tr { } impl Tr for Z { }
impl Q for Z { }
pub struct B { pub b: u8 }
impl U<Z> for Z {
    proof fn lm0(&self) { }
}
impl Q for B { }
pub struct Z { pub z: u8 }
impl Tr for B { }
pub mod m1 {
use crate::*;
impl U<B> for A {
    proof fn lm0(&self) { }
}
}
pub trait Q { }
pub struct A { pub a: u8 }
impl U<B> for B {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) { }
}
} // verus!
