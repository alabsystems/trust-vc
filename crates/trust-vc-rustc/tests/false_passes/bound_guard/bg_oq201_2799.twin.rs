verus!{
pub use m1::*;
pub use m1::m2::*;
pub fn gx<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.x() }
pub mod m1 {
use crate::*;
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
    proof fn l(&self) { self.w.l(); }
}
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
pub mod m2 {
use crate::*;
pub proof fn pl() ensures sp() == 7 { }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { self.x() }
    proof fn dm(&self) { }
}
}
}
pub trait Tr {
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for B {
    proof fn l(&self) { }
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
impl U for B {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { 7 }
    open spec fn m(&self) -> u8 { 7 }
}
pub struct W<X> { pub w: X }
impl Tr for A {
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
} // verus!
