verus!{
pub use m1::*;
impl U for B {
    fn z(&self) -> (r: u8) { 7 }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { 7 }
}
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.m() && r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
}
impl U for A {
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { 7 }
    open spec fn m(&self) -> u8 { 7 }
}
pub mod m1 {
use crate::*;
impl Tr for A {
    fn x(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
pub struct B { pub b: u8 }
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn tr(&self) -> (r: u8) ensures r == self.lim() { self.x() }
}
impl<X: Tr> Tr for W<X> {
    open spec fn lim(&self) -> u8 { self.w.lim() }
    fn x(&self) -> (r: u8) { self.w.x() }
}
}
pub struct W<X> { pub w: X }
pub struct A { pub a: u8 }
impl Tr for B {
    fn x(&self) -> (r: u8) { 7 }
    fn tr(&self) -> (r: u8) { 7 }
    open spec fn lim(&self) -> u8 { 7 }
}
} // verus!
