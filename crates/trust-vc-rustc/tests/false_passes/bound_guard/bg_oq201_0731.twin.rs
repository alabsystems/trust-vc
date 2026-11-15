verus!{
pub use m1::*;
pub use m1::m2::*;
pub proof fn pl() ensures sp() == 7 { }
pub mod m1 {
use crate::*;
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
impl Tr for B {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
    proof fn l(&self) { }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
    fn tr(&self) -> (r: u8) { 7 }
    proof fn l(&self) { }
}
pub mod m2 {
use crate::*;
pub fn gz<T: U>(t: &T) -> (r: u8) ensures r == t.lim() { t.z() }
impl U for B {
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.b }
    fn z(&self) -> (r: u8) { self.x() }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    fn tr(&self) -> (r: u8) ensures r == self.lim() { self.x() }
}
pub struct A { pub a: u8 }
}
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
}
pub struct B { pub b: u8 }
impl U for A {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { 7 }
    open spec fn m(&self) -> u8 { self.a }
}
pub fn ugz() { let r = gz(&A { a: 4 }); assert(r == 7); }
} // verus!
