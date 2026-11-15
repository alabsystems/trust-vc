verus!{
pub mod m1 {
use crate::*;
impl Tr for A { }
}
pub struct A { pub a: u8 } impl Tr for B { } impl Q for B { }
pub struct Z { pub z: u8 }
impl U<B> for A {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Q { }
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
impl Q for Z { }
}
pub proof fn fZ() { <Z as U<A>>::lm0(&(Z { z: 0 })); }
impl Q for A { }
impl U<Z> for B {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    fn dd(&self) -> (r: u8) where T: Tr { self.z1() }
}
impl U<A> for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Tr for Z { }
} // verus!
