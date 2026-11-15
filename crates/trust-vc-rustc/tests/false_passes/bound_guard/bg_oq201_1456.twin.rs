verus!{
pub use m1::*;
impl Tr for B {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
}
pub mod m1 {
use crate::*;
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
pub struct A { pub a: u8 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn tr(&self) -> (r: u8) { self.x() }
}
pub struct B { pub b: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
} // verus!
