verus!{
pub use m1::*;
pub use m1::m2::*;
pub struct B { pub b: u8 }
pub trait U: Tr {
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    spec fn m(&self) -> u8;
    open spec fn mm(&self) -> u8 { 2 }
    proof fn dm(&self) { self.lm(); }
    fn du(&self) -> (r: u8) { self.x() }
    proof fn lm(&self) ensures self.mm() == 2;
}
pub mod m1 {
use crate::*;
pub struct A { pub a: u8 }
impl Tr for A {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
pub mod m2 {
use crate::*;
pub fn uz() { let v = A { a: 5 }; let r = v.z(); assert(r == 7); }
pub proof fn pm() { let v = A { a: 1 }; v.lm(); assert(v.mm() == 2); }
pub proof fn pl() ensures sp() == 7 { }
}
}
impl Tr for B {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
impl U for A {
    fn z(&self) -> (r: u8) { 7 }
    fn du(&self) -> (r: u8) { 7 }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { 7 }
}
} // verus!
