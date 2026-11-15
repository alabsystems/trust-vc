verus!{
pub use m1::*;
pub use m1::m2::*;
impl Tr for A {
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
impl Tr for B {
    fn x(&self) -> (r: u8) { 7 }
    proof fn l(&self) { }
    open spec fn lim(&self) -> u8 { 7 }
}
pub open spec fn sp() -> u8 { (A { a: 1 }).lim() }
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) { let _q = self.x(); self.z() }
    proof fn dl(&self) { self.l(); }
    proof fn dm(&self) { }
}
impl U for B {
    open spec fn m(&self) -> u8 { self.b }
    proof fn lm(&self) { }
    fn z(&self) -> (r: u8) { 7 }
    fn du(&self) -> (r: u8) { 7 }
}
pub proof fn pl() ensures sp() == 7 { }
pub mod m2 {
use crate::*;
pub struct B { pub b: u8 }
pub trait Tr {
    fn x(&self) -> (r: u8) ensures r == self.lim();
    proof fn l(&self) ensures self.lim() == self.lim() + 0;
    spec fn lim(&self) -> u8;
}
}
}
} // verus!
