verus!{
pub struct A { pub a: u8 }
impl Tr for A { }
pub mod m2 {
use crate::*;
impl Tr for B { }
}
impl Q for B { }
impl Q for A { }
pub trait Q: Tr { }
impl U<A> for B {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
impl Tr for Z { }
pub proof fn fA() { <A as U<B>>::lm0(&(A { a: 0 })); }
impl U<Z> for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl U<B> for A {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Q { 2 }
    proof fn lm0(&self) where T: Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where T: Q ensures r == self.mm();
}
pub struct B { pub b: u8 }
pub trait Tr { }
} // verus!
