verus!{
pub use m1::*;
pub use m1::m2::*;
pub struct A { pub a: u8 }
pub mod m1 {
use crate::*;
pub trait U: Tr {
    spec fn m(&self) -> u8;
    fn z(&self) -> (r: u8) ensures r == self.lim();
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    fn du(&self) -> (r: u8) ensures r == self.lim() { self.z() }
    proof fn dm(&self) { self.lm(); }
}
pub mod m2 {
use crate::*;
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn x(&self) -> (r: u8) ensures r == self.lim();
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { 7 }
    fn x(&self) -> (r: u8) { 7 }
}
}
}
impl U for A {
    fn z(&self) -> (r: u8) { 7 }
    proof fn lm(&self) { }
    open spec fn m(&self) -> u8 { self.a }
}
} // verus!
