verus!{
pub mod m2 {
use crate::*;
impl U<Z> for A {
    proof fn lm1(&self) { }
    proof fn lm0(&self) { }
}
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn lm1(&self) where T: Tr + Q ensures self.mm() == 2;
    proof fn dd(&self) where T: Tr + Q { self.lm1(); }
}
pub mod m1 {
use crate::*;
impl Tr for Z { }
}
pub struct A { pub a: u8 }
impl U<Z> for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub trait Q: Tr { }
pub trait Tr { }
pub struct Z { pub z: u8 }
} // verus!
