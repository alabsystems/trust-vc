verus!{
pub use m1::*;
pub use m1::m2::*;
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
}
pub mod m1 {
use crate::*;
impl Tr for A {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.m();
    spec fn m(&self) -> u8;
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
}
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.m() { t.z() }
pub struct W<X> { pub w: X }
pub mod m2 {
use crate::*;
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 4); }
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
}
}
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 7); }
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
    fn tr(&self) -> (r: u8) { self.x() }
}
} // verus!
