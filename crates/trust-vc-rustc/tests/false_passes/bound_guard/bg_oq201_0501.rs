verus!{
pub use m1::*;
pub use m1::m2::*;
pub mod m1 {
use crate::*;
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
pub mod m2 {
use crate::*;
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { self.b }
}
pub struct A { pub a: u8 }
}
}
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    fn du(&self) -> (r: u8) { let _q = self.z(); self.x() }
    proof fn dm(&self) { self.lm(); }
    proof fn lm(&self) ensures self.mm() == 2;
    fn z(&self) -> (r: u8) ensures r == self.m();
    spec fn m(&self) -> u8;
}
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.a }
    fn du(&self) -> (r: u8) { self.a }
}
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub proof fn pl() ensures sp() == 1 { }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { self.a }
}
} // verus!
