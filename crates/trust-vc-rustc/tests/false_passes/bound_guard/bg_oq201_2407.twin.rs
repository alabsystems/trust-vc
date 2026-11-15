verus!{
pub use m1::*;
pub use m1::m2::*;
pub fn uw() { let v = W { w: A { a: 6 } }; let r = v.x(); assert(r == 7); }
pub struct A { pub a: u8 }
impl U for A {
    fn z(&self) -> (r: u8) { 7 }
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { 7 }
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { 7 }
}
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    fn z(&self) -> (r: u8) { 7 }
    proof fn lm(&self) { }
}
pub mod m1 {
use crate::*;
pub struct B { pub b: u8 }
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    proof fn l(&self) { self.w.l(); }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
    proof fn l(&self) { }
}
pub struct W<X> { pub w: X }
pub mod m2 {
use crate::*;
pub trait Tr {
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    spec fn lim(&self) -> u8;
    fn tr(&self) -> (r: u8) ensures r == self.lim() { self.x() }
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) ensures r == self.lim() { self.z() }
    proof fn dm(&self) { }
}
}
}
} // verus!
