verus!{
pub use m1::*;
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { let _q = self.z(); self.x() }
    proof fn dm(&self) { self.lm(); }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub mod m1 {
use crate::*;
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
}
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
pub struct A { pub a: u8 }
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub struct W<X> { pub w: X }
}
} // verus!
