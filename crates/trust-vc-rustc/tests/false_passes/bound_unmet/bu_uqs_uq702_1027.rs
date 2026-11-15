verus!{
impl Tr for A { }
pub struct A { pub a: u8 }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Tr for B { }
impl U<B> for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
impl Q for Z { }
pub proof fn fZ() { <Z as U<Z>>::lm1(&(Z { z: 0 })); }
pub struct B { pub b: u8 }
impl Tr for Z { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr + Q ensures self.mm() == 2;
}
impl Q for B { }
pub mod m2 {
use crate::*;
impl U<A> for B {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
}
pub trait Q: Tr { }
impl U<Z> for Z {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
} // verus!
