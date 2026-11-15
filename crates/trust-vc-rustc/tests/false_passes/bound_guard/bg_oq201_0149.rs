verus!{
pub use m1::*;
pub use m1::m2::*;
pub mod m1 {
use crate::*;
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
pub struct A { pub a: u8 }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dl(&self) { self.l(); }
    proof fn dm(&self) { self.lm(); }
}
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
pub mod m2 {
use crate::*;
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
impl Tr for A {
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
}
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    fn tr(&self) -> (r: u8) ensures r == self.lim() { self.x() }
}
} // verus!
