verus!{
pub use m1::*;
pub use m1::m2::*;
impl Tr for A {
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub struct B { pub b: u8 }
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 4); }
pub mod m1 {
use crate::*;
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    spec fn lim(&self) -> u8;
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
}
impl U for B {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { self.b }
    open spec fn m(&self) -> u8 { self.b }
}
impl Tr for B {
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { self.b }
    fn x(&self) -> (r: u8) { self.b }
}
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.z() }
pub mod m2 {
use crate::*;
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub struct A { pub a: u8 }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    fn du(&self) -> (r: u8) ensures r == self.lim() { self.z() }
    proof fn dl(&self) { self.l(); }
    spec fn m(&self) -> u8;
    proof fn dm(&self) { self.lm(); }
    fn z(&self) -> (r: u8) ensures r == self.lim();
    proof fn lm(&self) ensures self.mm() == 2;
}
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 5); }
}
}
pub proof fn pl() ensures sp() == 1 { }
impl U for A {
    open spec fn m(&self) -> u8 { self.a }
    fn z(&self) -> (r: u8) { self.x() }
    proof fn lm(&self) { }
}
} // verus!
