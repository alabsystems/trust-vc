verus!{
pub use m1::*;
pub use m1::m2::*;
impl U for B {
    fn z(&self) -> (r: u8) { self.b }
    open spec fn m(&self) -> u8 { self.b }
    proof fn lm(&self) { }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn z(&self) -> (r: u8) ensures r == self.m();
    fn du(&self) -> (r: u8) { self.x() }
    proof fn dm(&self) { }
}
pub mod m1 {
use crate::*;
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn tr(&self) -> (r: u8) { self.x() }
}
pub mod m2 {
use crate::*;
pub struct B { pub b: u8 }
}
}
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub struct A { pub a: u8 }
impl Tr for B {
    fn x(&self) -> (r: u8) { self.b }
    open spec fn lim(&self) -> u8 { self.b }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn x(&self) -> (r: u8) { self.a }
}
pub proof fn pl() ensures sp() == 1 { }
} // verus!
