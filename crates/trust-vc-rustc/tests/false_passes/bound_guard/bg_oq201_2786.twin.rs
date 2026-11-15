verus!{
pub use m1::*;
pub use m1::m2::*;
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { 2 }
    proof fn dm(&self) { self.lm(); }
}
impl U for A {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.a }
}
pub mod m1 {
use crate::*;
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub mod m2 {
use crate::*;
pub struct A { pub a: u8 }
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
}
pub fn ugx() { let r = gx(&A { a: 2 }); assert(r == 2); }
pub fn gx<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.x() }
}
}
pub fn ua() { let v = A { a: 5 }; let r = v.x(); assert(r == 5); }
} // verus!
