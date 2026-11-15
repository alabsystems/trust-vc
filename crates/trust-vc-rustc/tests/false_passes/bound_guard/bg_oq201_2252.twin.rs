verus!{
pub use m1::*;
pub use m1::m2::*;
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
impl U for A {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
}
pub mod m1 {
use crate::*;
impl<X: Tr> Tr for W<X> {
    proof fn l(&self) { self.w.l(); }
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn mm(&self) -> u8 { 2 }
    fn du(&self) -> (r: u8) { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { self.lm(); }
    proof fn dl(&self) { self.l(); }
    fn z(&self) -> (r: u8) ensures r == self.m();
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub struct W<X> { pub w: X }
pub mod m2 {
use crate::*;
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { self.b }
}
impl Tr for A {
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
}
}
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
} // verus!
