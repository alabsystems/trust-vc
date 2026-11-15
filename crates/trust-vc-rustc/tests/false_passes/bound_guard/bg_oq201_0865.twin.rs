verus!{
pub use m1::*;
pub use m1::m2::*;
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
}
pub proof fn pl() ensures sp() == 1 { }
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.a }
    proof fn lm(&self) { }
}
pub fn uw() { let v = W { w: A { a: 6 } }; let r = v.x(); assert(r == 6); }
impl U for B {
    fn z(&self) -> (r: u8) { self.b }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.b }
}
pub fn ugx() { let r = gx(&A { a: 2 }); assert(r == 2); }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub mod m1 {
use crate::*;
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
pub struct W<X> { pub w: X }
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub mod m2 {
use crate::*;
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
pub struct B { pub b: u8 }
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub struct A { pub a: u8 }
pub fn gx<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.x() }
}
}
pub fn uww() { let v = W { w: W { w: A { a: 3 } } }; let r = v.x(); assert(r == 3); }
} // verus!
