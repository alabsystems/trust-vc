verus!{
pub use m1::*;
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
pub struct A { pub a: u8 }
pub trait U: Tr {
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    fn du(&self) -> (r: u8) { let _q = self.z(); self.x() }
    open spec fn mm(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn dm(&self) { self.lm(); }
    proof fn lm(&self) ensures self.mm() == 2;
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn tr(&self) -> (r: u8) { self.x() }
}
impl U for B {
    fn z(&self) -> (r: u8) { self.b }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.b }
}
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
pub mod m1 {
use crate::*;
pub struct B { pub b: u8 }
pub proof fn pl() ensures sp() == 1 { }
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub struct W<X> { pub w: X }
}
} // verus!
