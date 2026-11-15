verus!{
pub use m1::*;
pub use m1::m2::*;
pub struct B { pub b: u8 }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.a }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub mod m1 {
use crate::*;
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
pub fn gx<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.x() }
pub mod m2 {
use crate::*;
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
}
}
pub fn ugx() { let r = gx(&A { a: 2 }); assert(r == 2); }
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) ensures r == self.m() { self.z() }
    proof fn dm(&self) { self.lm(); }
}
pub struct A { pub a: u8 }
} // verus!
