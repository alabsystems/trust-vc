verus!{
pub use m1::*;
pub use m1::m2::*;
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
}
impl U for B {
    fn z(&self) -> (r: u8) { self.b }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.b }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
pub mod m2 {
use crate::*;
pub struct B { pub b: u8 }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
}
}
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
} // verus!
