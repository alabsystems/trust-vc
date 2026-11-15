verus!{
pub use m1::*;
pub use m1::m2::*;
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    fn z(&self) -> (r: u8) { self.b }
    proof fn lm(&self) { }
}
pub struct A { pub a: u8 }
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub mod m1 {
use crate::*;
pub struct B { pub b: u8 }
pub struct W<X> { pub w: X }
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.a }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
    proof fn l(&self) { }
}
pub mod m2 {
use crate::*;
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { self.lm(); }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    fn tr(&self) -> (r: u8) { self.x() }
}
}
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { self.b }
}
pub proof fn pl() ensures sp() == 1 { }
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
    proof fn l(&self) { self.w.l(); }
}
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
} // verus!
