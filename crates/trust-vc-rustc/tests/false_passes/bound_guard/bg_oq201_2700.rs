verus!{
pub use m1::*;
pub use m1::m2::*;
impl U for B {
    fn z(&self) -> (r: u8) { 7 }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { 7 }
}
impl U for A {
    open spec fn m(&self) -> u8 { 7 }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { 7 }
}
pub struct B { pub b: u8 }
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
pub fn uww() { let v = W { w: W { w: A { a: 3 } } }; let r = v.x(); assert(r == 7); }
pub trait U: Tr {
    fn du(&self) -> (r: u8) { let _q = self.x(); self.z() }
    open spec fn mm(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn lm(&self) ensures self.mm() == 2;
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    proof fn dm(&self) { self.lm(); }
}
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
pub mod m1 {
use crate::*;
pub struct W<X> { pub w: X }
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
pub mod m2 {
use crate::*;
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 7); }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for B {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
pub struct A { pub a: u8 }
}
}
} // verus!
