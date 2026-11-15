verus!{
pub use m1::*;
pub use m1::m2::*;
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
    proof fn l(&self) { }
}
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
pub mod m2 {
use crate::*;
pub trait Tr {
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    proof fn lm(&self) ensures self.mm() == 2;
    fn z(&self) -> (r: u8) ensures r == self.m();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dm(&self) { }
}
}
}
} // verus!
