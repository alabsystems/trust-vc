verus!{
pub use m1::*;
pub use m1::m2::*;
impl<X: Tr> Tr for W<X> {
    fn x(&self) -> (r: u8) { self.w.x() }
    open spec fn lim(&self) -> u8 { self.w.lim() }
}
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
pub fn gx<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.x() }
pub fn ugx() { let r = gx(&A { a: 2 }); assert(r == 2); }
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub fn uw() { let v = W { w: A { a: 6 } }; let r = v.x(); assert(r == 6); }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn tr(&self) -> (r: u8) { 2 }
}
pub mod m1 {
use crate::*;
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
pub trait U: Tr {
    fn z(&self) -> (r: u8) ensures r == self.m();
    proof fn lm(&self) ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
    spec fn m(&self) -> u8;
    proof fn dm(&self) { self.lm(); }
}
pub struct A { pub a: u8 }
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
pub mod m2 {
use crate::*;
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
}
}
pub struct W<X> { pub w: X }
} // verus!
