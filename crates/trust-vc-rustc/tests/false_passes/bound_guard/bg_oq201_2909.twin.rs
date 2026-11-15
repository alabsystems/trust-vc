verus!{
pub use m1::*;
pub use m1::m2::*;
pub struct A { pub a: u8 }
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub mod m1 {
use crate::*;
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { let _q = self.z(); self.x() }
    proof fn dm(&self) { }
}
impl Tr for B {
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
pub struct B { pub b: u8 }
pub mod m2 {
use crate::*;
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
}
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.a }
    proof fn lm(&self) { }
}
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
} // verus!
