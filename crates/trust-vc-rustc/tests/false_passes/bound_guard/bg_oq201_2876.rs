verus!{
pub use m1::*;
pub use m1::m2::*;
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
pub mod m1 {
use crate::*;
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub struct B { pub b: u8 }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.m();
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) ensures r == self.m() { self.z() }
    spec fn m(&self) -> u8;
    proof fn dm(&self) { self.lm(); }
}
pub mod m2 {
use crate::*;
impl U for A {
    fn z(&self) -> (r: u8) { self.a }
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
}
pub struct A { pub a: u8 }
}
}
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
} // verus!
